import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R04864G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4864_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] := by
    let c9r4864targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c9r4864choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4864targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] c9r4864choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4864targets, c9r4864choice, ?_, checked⟩
    intro S h
    simp only [c9r4864targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 7 _ (by rfl)
  have c9r4865_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] := by
    let c9r4865targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c9r4865choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4865targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] c9r4865choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4865targets, c9r4865choice, ?_, checked⟩
    intro S h
    simp only [c9r4865targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 9 _ (by rfl)
  have c9r4866_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] := by
    let c9r4866targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)]]
    let c9r4866choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4866targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] c9r4866choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4866targets, c9r4866choice, ?_, checked⟩
    intro S h
    simp only [c9r4866targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 13 _ (by rfl)
  have c9r4867_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] := by
    let c9r4867targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)]]
    let c9r4867choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4867targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] c9r4867choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4867targets, c9r4867choice, ?_, checked⟩
    intro S h
    simp only [c9r4867targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 16 _ (by rfl)
  have c9r4868_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] := by
    let c9r4868targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]
    let c9r4868choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4868targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] c9r4868choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4868targets, c9r4868choice, ?_, checked⟩
    intro S h
    simp only [c9r4868targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 19 _ (by rfl)
  have c9r4869_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] := by
    let c9r4869targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c9r4869choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4869targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] c9r4869choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4869targets, c9r4869choice, ?_, checked⟩
    intro S h
    simp only [c9r4869targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 23 _ (by rfl)
  have c9r4870_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] := by
    let c9r4870targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c9r4870choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4870targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] c9r4870choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4870targets, c9r4870choice, ?_, checked⟩
    intro S h
    simp only [c9r4870targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 26 _ (by rfl)
  have c9r4871_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] := by
    let c9r4871targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c9r4871choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4871targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] c9r4871choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4871targets, c9r4871choice, ?_, checked⟩
    intro S h
    simp only [c9r4871targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4864_closed
  · subst row; exact c9r4865_closed
  · subst row; exact c9r4866_closed
  · subst row; exact c9r4867_closed
  · subst row; exact c9r4868_closed
  · subst row; exact c9r4869_closed
  · subst row; exact c9r4870_closed
  · subst row; exact c9r4871_closed
theorem C9R04864G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4872_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] := by
    let c9r4872targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c9r4872choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4872targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] c9r4872choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4872targets, c9r4872choice, ?_, checked⟩
    intro S h
    simp only [c9r4872targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 0 _ (by rfl)
  have c9r4873_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] := by
    let c9r4873targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c9r4873choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4873targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] c9r4873choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4873targets, c9r4873choice, ?_, checked⟩
    intro S h
    simp only [c9r4873targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 3 _ (by rfl)
  have c9r4874_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] := by
    let c9r4874targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)]]
    let c9r4874choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4874targets [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)] c9r4874choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4874targets, c9r4874choice, ?_, checked⟩
    intro S h
    simp only [c9r4874targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 6 _ (by rfl)
  have c9r4875_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] := by
    let c9r4875targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)]]
    let c9r4875choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4875targets [(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] c9r4875choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4875targets, c9r4875choice, ?_, checked⟩
    intro S h
    simp only [c9r4875targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 12 _ (by rfl)
  have c9r4876_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r4876targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r4876choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4876targets [(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r4876choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4876targets, c9r4876choice, ?_, checked⟩
    intro S h
    simp only [c9r4876targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 17 _ (by rfl)
  have c9r4877_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r4877targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r4877choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4877targets [(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)] c9r4877choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4877targets, c9r4877choice, ?_, checked⟩
    intro S h
    simp only [c9r4877targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 22 _ (by rfl)
  have c9r4878_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r4878targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r4878choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4878targets [(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)] c9r4878choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4878targets, c9r4878choice, ?_, checked⟩
    intro S h
    simp only [c9r4878targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 26 _ (by rfl)
  have c9r4879_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r4879targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r4879choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4879targets [(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)] c9r4879choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4879targets, c9r4879choice, ?_, checked⟩
    intro S h
    simp only [c9r4879targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4872_closed
  · subst row; exact c9r4873_closed
  · subst row; exact c9r4874_closed
  · subst row; exact c9r4875_closed
  · subst row; exact c9r4876_closed
  · subst row; exact c9r4877_closed
  · subst row; exact c9r4878_closed
  · subst row; exact c9r4879_closed
theorem C9R04864G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4880_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r4880targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r4880choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4880targets [(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)] c9r4880choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4880targets, c9r4880choice, ?_, checked⟩
    intro S h
    simp only [c9r4880targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,true,true] 30 _ (by rfl)
  have c9r4881_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] := by
    let c9r4881targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,3),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)]]
    let c9r4881choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4881targets [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] c9r4881choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4881targets, c9r4881choice, ?_, checked⟩
    intro S h
    simp only [c9r4881targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 6 _ (by rfl)
  have c9r4882_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r4882targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r4882choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4882targets [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c9r4882choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4882targets, c9r4882choice, ?_, checked⟩
    intro S h
    simp only [c9r4882targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 12 _ (by rfl)
  have c9r4883_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] := by
    let c9r4883targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)]]
    let c9r4883choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4883targets [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] c9r4883choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4883targets, c9r4883choice, ?_, checked⟩
    intro S h
    simp only [c9r4883targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 16 _ (by rfl)
  have c9r4884_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] := by
    let c9r4884targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)]]
    let c9r4884choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4884targets [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] c9r4884choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4884targets, c9r4884choice, ?_, checked⟩
    intro S h
    simp only [c9r4884targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 20 _ (by rfl)
  have c9r4885_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] := by
    let c9r4885targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c9r4885choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4885targets [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] c9r4885choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4885targets, c9r4885choice, ?_, checked⟩
    intro S h
    simp only [c9r4885targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 22 _ (by rfl)
  have c9r4886_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c9r4886targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c9r4886choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4886targets [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] c9r4886choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4886targets, c9r4886choice, ?_, checked⟩
    intro S h
    simp only [c9r4886targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 24 _ (by rfl)
  have c9r4887_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] := by
    let c9r4887targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)]]
    let c9r4887choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4887targets [(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)] c9r4887choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4887targets, c9r4887choice, ?_, checked⟩
    intro S h
    simp only [c9r4887targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4880_closed
  · subst row; exact c9r4881_closed
  · subst row; exact c9r4882_closed
  · subst row; exact c9r4883_closed
  · subst row; exact c9r4884_closed
  · subst row; exact c9r4885_closed
  · subst row; exact c9r4886_closed
  · subst row; exact c9r4887_closed
theorem C9R04864G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4888_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r4888targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r4888choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4888targets [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r4888choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4888targets, c9r4888choice, ?_, checked⟩
    intro S h
    simp only [c9r4888targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 5 _ (by rfl)
  have c9r4889_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r4889targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r4889choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4889targets [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c9r4889choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4889targets, c9r4889choice, ?_, checked⟩
    intro S h
    simp only [c9r4889targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 8 _ (by rfl)
  have c9r4890_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r4890targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r4890choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4890targets [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] c9r4890choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4890targets, c9r4890choice, ?_, checked⟩
    intro S h
    simp only [c9r4890targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 10 _ (by rfl)
  have c9r4891_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r4891targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r4891choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4891targets [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] c9r4891choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4891targets, c9r4891choice, ?_, checked⟩
    intro S h
    simp only [c9r4891targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 12 _ (by rfl)
  have c9r4892_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] := by
    let c9r4892targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)]]
    let c9r4892choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4892targets [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)] c9r4892choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4892targets, c9r4892choice, ?_, checked⟩
    intro S h
    simp only [c9r4892targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 17 _ (by rfl)
  have c9r4893_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] := by
    let c9r4893targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)]]
    let c9r4893choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4893targets [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)] c9r4893choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4893targets, c9r4893choice, ?_, checked⟩
    intro S h
    simp only [c9r4893targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 20 _ (by rfl)
  have c9r4894_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] := by
    let c9r4894targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)]]
    let c9r4894choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4894targets [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)] c9r4894choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4894targets, c9r4894choice, ?_, checked⟩
    intro S h
    simp only [c9r4894targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 23 _ (by rfl)
  have c9r4895_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)] := by
    let c9r4895targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)]]
    let c9r4895choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4895targets [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)] c9r4895choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4895targets, c9r4895choice, ?_, checked⟩
    intro S h
    simp only [c9r4895targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4888_closed
  · subst row; exact c9r4889_closed
  · subst row; exact c9r4890_closed
  · subst row; exact c9r4891_closed
  · subst row; exact c9r4892_closed
  · subst row; exact c9r4893_closed
  · subst row; exact c9r4894_closed
  · subst row; exact c9r4895_closed
theorem C9R04864_closed (row : List GridPoint) (h : FamilyMember row F9B002L24) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L24, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R04864G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04864G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04864G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04864G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04864G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04864G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04864G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04864G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04864G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04864G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04864G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04864G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04864G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04864G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04864G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04864G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04864G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04864G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04864G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04864G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04864G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04864G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04864G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04864G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04864G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04864G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04864G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04864G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04864G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04864G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04864G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04864G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
