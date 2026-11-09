import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R07744G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7744_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)] := by
    let c9r7744targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)]]
    let c9r7744choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7744targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)] c9r7744choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7744targets, c9r7744choice, ?_, checked⟩
    intro S h
    simp only [c9r7744targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 12 _ (by rfl)
  have c9r7745_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)] := by
    let c9r7745targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c9r7745choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7745targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)] c9r7745choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7745targets, c9r7745choice, ?_, checked⟩
    intro S h
    simp only [c9r7745targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 15 _ (by rfl)
  have c9r7746_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r7746targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r7746choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7746targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)] c9r7746choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7746targets, c9r7746choice, ?_, checked⟩
    intro S h
    simp only [c9r7746targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 19 _ (by rfl)
  have c9r7747_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)] := by
    let c9r7747targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c9r7747choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7747targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)] c9r7747choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7747targets, c9r7747choice, ?_, checked⟩
    intro S h
    simp only [c9r7747targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 24 _ (by rfl)
  have c9r7748_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)] := by
    let c9r7748targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c9r7748choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7748targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)] c9r7748choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7748targets, c9r7748choice, ?_, checked⟩
    intro S h
    simp only [c9r7748targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 26 _ (by rfl)
  have c9r7749_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)] := by
    let c9r7749targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c9r7749choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7749targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)] c9r7749choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7749targets, c9r7749choice, ?_, checked⟩
    intro S h
    simp only [c9r7749targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 28 _ (by rfl)
  have c9r7750_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)] := by
    let c9r7750targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)]]
    let c9r7750choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r7750targets [(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)] c9r7750choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7750targets, c9r7750choice, ?_, checked⟩
    intro S h
    simp only [c9r7750targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 0 _ (by rfl)
  have c9r7751_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)] := by
    let c9r7751targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)]]
    let c9r7751choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7751targets [(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)] c9r7751choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7751targets, c9r7751choice, ?_, checked⟩
    intro S h
    simp only [c9r7751targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7744_closed
  · subst row; exact c9r7745_closed
  · subst row; exact c9r7746_closed
  · subst row; exact c9r7747_closed
  · subst row; exact c9r7748_closed
  · subst row; exact c9r7749_closed
  · subst row; exact c9r7750_closed
  · subst row; exact c9r7751_closed
theorem C9R07744G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7752_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r7752targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r7752choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7752targets [(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r7752choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7752targets, c9r7752choice, ?_, checked⟩
    intro S h
    simp only [c9r7752targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 14 _ (by rfl)
  have c9r7753_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r7753targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r7753choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7753targets [(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)] c9r7753choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7753targets, c9r7753choice, ?_, checked⟩
    intro S h
    simp only [c9r7753targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 17 _ (by rfl)
  have c9r7754_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r7754targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r7754choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7754targets [(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)] c9r7754choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7754targets, c9r7754choice, ?_, checked⟩
    intro S h
    simp only [c9r7754targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 19 _ (by rfl)
  have c9r7755_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r7755targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r7755choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7755targets [(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)] c9r7755choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7755targets, c9r7755choice, ?_, checked⟩
    intro S h
    simp only [c9r7755targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 21 _ (by rfl)
  have c9r7756_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r7756targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r7756choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7756targets [(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] c9r7756choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7756targets, c9r7756choice, ?_, checked⟩
    intro S h
    simp only [c9r7756targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 26 _ (by rfl)
  have c9r7757_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r7757targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r7757choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7757targets [(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] c9r7757choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7757targets, c9r7757choice, ?_, checked⟩
    intro S h
    simp only [c9r7757targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 0 _ (by rfl)
  have c9r7758_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r7758targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r7758choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7758targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r7758choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7758targets, c9r7758choice, ?_, checked⟩
    intro S h
    simp only [c9r7758targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 10 _ (by rfl)
  have c9r7759_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r7759targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r7759choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7759targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r7759choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7759targets, c9r7759choice, ?_, checked⟩
    intro S h
    simp only [c9r7759targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7752_closed
  · subst row; exact c9r7753_closed
  · subst row; exact c9r7754_closed
  · subst row; exact c9r7755_closed
  · subst row; exact c9r7756_closed
  · subst row; exact c9r7757_closed
  · subst row; exact c9r7758_closed
  · subst row; exact c9r7759_closed
theorem C9R07744G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7760_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r7760targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r7760choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7760targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r7760choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7760targets, c9r7760choice, ?_, checked⟩
    intro S h
    simp only [c9r7760targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 17 _ (by rfl)
  have c9r7761_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r7761targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r7761choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7761targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r7761choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7761targets, c9r7761choice, ?_, checked⟩
    intro S h
    simp only [c9r7761targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 19 _ (by rfl)
  have c9r7762_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r7762targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r7762choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7762targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r7762choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7762targets, c9r7762choice, ?_, checked⟩
    intro S h
    simp only [c9r7762targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 21 _ (by rfl)
  have c9r7763_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r7763targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r7763choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7763targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r7763choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7763targets, c9r7763choice, ?_, checked⟩
    intro S h
    simp only [c9r7763targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 24 _ (by rfl)
  have c9r7764_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r7764targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r7764choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7764targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r7764choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7764targets, c9r7764choice, ?_, checked⟩
    intro S h
    simp only [c9r7764targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 27 _ (by rfl)
  have c9r7765_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r7765targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r7765choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7765targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r7765choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7765targets, c9r7765choice, ?_, checked⟩
    intro S h
    simp only [c9r7765targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 29 _ (by rfl)
  have c9r7766_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r7766targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r7766choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7766targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r7766choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7766targets, c9r7766choice, ?_, checked⟩
    intro S h
    simp only [c9r7766targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 0 _ (by rfl)
  have c9r7767_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r7767targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r7767choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7767targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r7767choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7767targets, c9r7767choice, ?_, checked⟩
    intro S h
    simp only [c9r7767targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7760_closed
  · subst row; exact c9r7761_closed
  · subst row; exact c9r7762_closed
  · subst row; exact c9r7763_closed
  · subst row; exact c9r7764_closed
  · subst row; exact c9r7765_closed
  · subst row; exact c9r7766_closed
  · subst row; exact c9r7767_closed
theorem C9R07744G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7768_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r7768targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r7768choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7768targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r7768choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7768targets, c9r7768choice, ?_, checked⟩
    intro S h
    simp only [c9r7768targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 6 _ (by rfl)
  have c9r7769_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r7769targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r7769choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7769targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r7769choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7769targets, c9r7769choice, ?_, checked⟩
    intro S h
    simp only [c9r7769targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 9 _ (by rfl)
  have c9r7770_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r7770targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r7770choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7770targets [(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)] c9r7770choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7770targets, c9r7770choice, ?_, checked⟩
    intro S h
    simp only [c9r7770targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 14 _ (by rfl)
  have c9r7771_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r7771targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r7771choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7771targets [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r7771choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7771targets, c9r7771choice, ?_, checked⟩
    intro S h
    simp only [c9r7771targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 19 _ (by rfl)
  have c9r7772_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r7772targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r7772choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7772targets [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)] c9r7772choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7772targets, c9r7772choice, ?_, checked⟩
    intro S h
    simp only [c9r7772targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 24 _ (by rfl)
  have c9r7773_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c9r7773targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c9r7773choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7773targets [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)] c9r7773choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7773targets, c9r7773choice, ?_, checked⟩
    intro S h
    simp only [c9r7773targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 26 _ (by rfl)
  have c9r7774_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c9r7774targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c9r7774choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7774targets [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)] c9r7774choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7774targets, c9r7774choice, ?_, checked⟩
    intro S h
    simp only [c9r7774targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 28 _ (by rfl)
  have c9r7775_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)] := by
    let c9r7775targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)]]
    let c9r7775choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7775targets [(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)] c9r7775choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7775targets, c9r7775choice, ?_, checked⟩
    intro S h
    simp only [c9r7775targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7768_closed
  · subst row; exact c9r7769_closed
  · subst row; exact c9r7770_closed
  · subst row; exact c9r7771_closed
  · subst row; exact c9r7772_closed
  · subst row; exact c9r7773_closed
  · subst row; exact c9r7774_closed
  · subst row; exact c9r7775_closed
theorem C9R07744_closed (row : List GridPoint) (h : FamilyMember row F9B003L50) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L50, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R07744G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07744G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07744G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07744G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07744G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07744G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07744G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07744G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07744G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07744G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07744G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07744G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07744G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07744G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07744G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07744G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07744G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07744G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07744G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07744G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07744G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07744G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07744G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07744G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07744G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07744G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07744G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07744G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07744G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07744G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07744G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07744G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
