import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08864G0 (row : List GridPoint) (h : row ∈ [[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8864_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c9r8864targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c9r8864choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8864targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)] c9r8864choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8864targets, c9r8864choice, ?_, checked⟩
    intro S h
    simp only [c9r8864targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 13 _ (by rfl)
  have c9r8865_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)] := by
    let c9r8865targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(3,5)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,1),(1,2),(1,3),(1,5),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(2,6)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(2,6)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,5)]]
    let c9r8865choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8865targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5)] c9r8865choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8865targets, c9r8865choice, ?_, checked⟩
    intro S h
    simp only [c9r8865targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 19 _ (by rfl)
  have c9r8866_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)] := by
    let c9r8866targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(4,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(2,5),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(4,0)]]
    let c9r8866choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8866targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0)] c9r8866choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8866targets, c9r8866choice, ?_, checked⟩
    intro S h
    simp only [c9r8866targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 23 _ (by rfl)
  have c9r8867_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)] := by
    let c9r8867targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(4,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(4,1)]]
    let c9r8867choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8867targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1)] c9r8867choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8867targets, c9r8867choice, ?_, checked⟩
    intro S h
    simp only [c9r8867targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 27 _ (by rfl)
  have c9r8868_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)] := by
    let c9r8868targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(4,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3),(4,3)]]
    let c9r8868choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8868targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3)] c9r8868choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8868targets, c9r8868choice, ?_, checked⟩
    intro S h
    simp only [c9r8868targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 30 _ (by rfl)
  have c9r8869_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)] := by
    let c9r8869targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4),(4,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,5)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4),(3,5)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4),(4,4)]]
    let c9r8869choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8869targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,4)] c9r8869choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8869targets, c9r8869choice, ?_, checked⟩
    intro S h
    simp only [c9r8869targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 0 _ (by rfl)
  have c9r8870_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)] := by
    let c9r8870targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0),(4,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(4,1)]]
    let c9r8870choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8870targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1)] c9r8870choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8870targets, c9r8870choice, ?_, checked⟩
    intro S h
    simp only [c9r8870targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 4 _ (by rfl)
  have c9r8871_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)] := by
    let c9r8871targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0),(4,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3),(4,3)]]
    let c9r8871choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8871targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)] c9r8871choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8871targets, c9r8871choice, ?_, checked⟩
    intro S h
    simp only [c9r8871targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8864_closed
  · subst row; exact c9r8865_closed
  · subst row; exact c9r8866_closed
  · subst row; exact c9r8867_closed
  · subst row; exact c9r8868_closed
  · subst row; exact c9r8869_closed
  · subst row; exact c9r8870_closed
  · subst row; exact c9r8871_closed
theorem C9R08864G1 (row : List GridPoint) (h : row ∈ [[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8872_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)] := by
    let c9r8872targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0),(5,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,0),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0),(5,0)]]
    let c9r8872choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8872targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0)] c9r8872choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8872targets, c9r8872choice, ?_, checked⟩
    intro S h
    simp only [c9r8872targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 10 _ (by rfl)
  have c9r8873_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)] := by
    let c9r8873targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(4,2)]]
    let c9r8873choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r8873targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2)] c9r8873choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8873targets, c9r8873choice, ?_, checked⟩
    intro S h
    simp only [c9r8873targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 13 _ (by rfl)
  have c9r8874_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)] := by
    let c9r8874targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(4,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3),(4,3)]]
    let c9r8874choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8874targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3)] c9r8874choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8874targets, c9r8874choice, ?_, checked⟩
    intro S h
    simp only [c9r8874targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 16 _ (by rfl)
  have c9r8875_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)] := by
    let c9r8875targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(5,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1),(5,1)]]
    let c9r8875choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8875targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)] c9r8875choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8875targets, c9r8875choice, ?_, checked⟩
    intro S h
    simp only [c9r8875targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 19 _ (by rfl)
  have c9r8876_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)] := by
    let c9r8876targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,2),(4,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3),(4,3)]]
    let c9r8876choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8876targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)] c9r8876choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8876targets, c9r8876choice, ?_, checked⟩
    intro S h
    simp only [c9r8876targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 22 _ (by rfl)
  have c9r8877_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)] := by
    let c9r8877targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3),(4,4)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4),(3,5)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4),(3,5)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4),(4,4)]]
    let c9r8877choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8877targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)] c9r8877choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8877targets, c9r8877choice, ?_, checked⟩
    intro S h
    simp only [c9r8877targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 25 _ (by rfl)
  have c9r8878_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)] := by
    let c9r8878targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3),(5,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4),(4,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3),(4,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3),(5,3)]]
    let c9r8878choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8878targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)] c9r8878choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8878targets, c9r8878choice, ?_, checked⟩
    intro S h
    simp only [c9r8878targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 28 _ (by rfl)
  have c9r8879_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c9r8879targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c9r8879choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8879targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)] c9r8879choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8879targets, c9r8879choice, ?_, checked⟩
    intro S h
    simp only [c9r8879targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8872_closed
  · subst row; exact c9r8873_closed
  · subst row; exact c9r8874_closed
  · subst row; exact c9r8875_closed
  · subst row; exact c9r8876_closed
  · subst row; exact c9r8877_closed
  · subst row; exact c9r8878_closed
  · subst row; exact c9r8879_closed
theorem C9R08864G2 (row : List GridPoint) (h : row ∈ [[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8880_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c9r8880targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c9r8880choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8880targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)] c9r8880choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8880targets, c9r8880choice, ?_, checked⟩
    intro S h
    simp only [c9r8880targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 2 _ (by rfl)
  have c9r8881_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c9r8881targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c9r8881choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8881targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)] c9r8881choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8881targets, c9r8881choice, ?_, checked⟩
    intro S h
    simp only [c9r8881targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 4 _ (by rfl)
  have c9r8882_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c9r8882targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c9r8882choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8882targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)] c9r8882choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8882targets, c9r8882choice, ?_, checked⟩
    intro S h
    simp only [c9r8882targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 7 _ (by rfl)
  have c9r8883_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c9r8883targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(4,0),(5,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c9r8883choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8883targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)] c9r8883choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8883targets, c9r8883choice, ?_, checked⟩
    intro S h
    simp only [c9r8883targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 9 _ (by rfl)
  have c9r8884_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c9r8884targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c9r8884choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8884targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)] c9r8884choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8884targets, c9r8884choice, ?_, checked⟩
    intro S h
    simp only [c9r8884targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 13 _ (by rfl)
  have c9r8885_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c9r8885targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c9r8885choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8885targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)] c9r8885choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8885targets, c9r8885choice, ?_, checked⟩
    intro S h
    simp only [c9r8885targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 16 _ (by rfl)
  have c9r8886_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c9r8886targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c9r8886choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8886targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)] c9r8886choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8886targets, c9r8886choice, ?_, checked⟩
    intro S h
    simp only [c9r8886targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 18 _ (by rfl)
  have c9r8887_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c9r8887targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c9r8887choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8887targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)] c9r8887choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8887targets, c9r8887choice, ?_, checked⟩
    intro S h
    simp only [c9r8887targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8880_closed
  · subst row; exact c9r8881_closed
  · subst row; exact c9r8882_closed
  · subst row; exact c9r8883_closed
  · subst row; exact c9r8884_closed
  · subst row; exact c9r8885_closed
  · subst row; exact c9r8886_closed
  · subst row; exact c9r8887_closed
theorem C9R08864G3 (row : List GridPoint) (h : row ∈ [[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8888_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c9r8888targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c9r8888choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r8888targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)] c9r8888choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8888targets, c9r8888choice, ?_, checked⟩
    intro S h
    simp only [c9r8888targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 24 _ (by rfl)
  have c9r8889_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c9r8889targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c9r8889choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8889targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)] c9r8889choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8889targets, c9r8889choice, ?_, checked⟩
    intro S h
    simp only [c9r8889targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 27 _ (by rfl)
  have c9r8890_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r8890targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r8890choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8890targets [(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)] c9r8890choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8890targets, c9r8890choice, ?_, checked⟩
    intro S h
    simp only [c9r8890targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 0 _ (by rfl)
  have c9r8891_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r8891targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r8891choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r8891targets [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r8891choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8891targets, c9r8891choice, ?_, checked⟩
    intro S h
    simp only [c9r8891targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 6 _ (by rfl)
  have c9r8892_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r8892targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r8892choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r8892targets [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)] c9r8892choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8892targets, c9r8892choice, ?_, checked⟩
    intro S h
    simp only [c9r8892targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 11 _ (by rfl)
  have c9r8893_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c9r8893targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c9r8893choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r8893targets [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)] c9r8893choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8893targets, c9r8893choice, ?_, checked⟩
    intro S h
    simp only [c9r8893targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 13 _ (by rfl)
  have c9r8894_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c9r8894targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c9r8894choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r8894targets [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)] c9r8894choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8894targets, c9r8894choice, ?_, checked⟩
    intro S h
    simp only [c9r8894targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 15 _ (by rfl)
  have c9r8895_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c9r8895targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c9r8895choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r8895targets [(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)] c9r8895choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8895targets, c9r8895choice, ?_, checked⟩
    intro S h
    simp only [c9r8895targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8888_closed
  · subst row; exact c9r8889_closed
  · subst row; exact c9r8890_closed
  · subst row; exact c9r8891_closed
  · subst row; exact c9r8892_closed
  · subst row; exact c9r8893_closed
  · subst row; exact c9r8894_closed
  · subst row; exact c9r8895_closed
theorem C9R08864_closed (row : List GridPoint) (h : FamilyMember row F9B004L21) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L21, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08864G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08864G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08864G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08864G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08864G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08864G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08864G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08864G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08864G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08864G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08864G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08864G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08864G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08864G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08864G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08864G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08864G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08864G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08864G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08864G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08864G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08864G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08864G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08864G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08864G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08864G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08864G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08864G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08864G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08864G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08864G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08864G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
