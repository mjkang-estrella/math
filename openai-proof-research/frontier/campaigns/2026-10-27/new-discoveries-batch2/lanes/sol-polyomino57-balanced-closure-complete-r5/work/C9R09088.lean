import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R09088G0 (row : List GridPoint) (h : row ∈ [[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9088_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r9088targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,3),(1,4),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r9088choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9088targets [(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r9088choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9088targets, c9r9088choice, ?_, checked⟩
    intro S h
    simp only [c9r9088targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 20 _ (by rfl)
  have c9r9089_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r9089targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,4),(1,3),(1,4),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,4),(1,3),(1,4),(2,3),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r9089choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9089targets [(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r9089choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9089targets, c9r9089choice, ?_, checked⟩
    intro S h
    simp only [c9r9089targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 23 _ (by rfl)
  have c9r9090_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r9090targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,4),(1,3),(1,4),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r9090choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9090targets [(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r9090choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9090targets, c9r9090choice, ?_, checked⟩
    intro S h
    simp only [c9r9090targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 25 _ (by rfl)
  have c9r9091_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r9091targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,4),(1,3),(1,4),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r9091choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9091targets [(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r9091choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9091targets, c9r9091choice, ?_, checked⟩
    intro S h
    simp only [c9r9091targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 27 _ (by rfl)
  have c9r9092_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r9092targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,4),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r9092choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9092targets [(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)] c9r9092choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9092targets, c9r9092choice, ?_, checked⟩
    intro S h
    simp only [c9r9092targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 0 _ (by rfl)
  have c9r9093_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r9093targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,4),(1,3),(1,4),(2,3),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r9093choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9093targets [(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)] c9r9093choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9093targets, c9r9093choice, ?_, checked⟩
    intro S h
    simp only [c9r9093targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 6 _ (by rfl)
  have c9r9094_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9094targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9094choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9094targets [(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)] c9r9094choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9094targets, c9r9094choice, ?_, checked⟩
    intro S h
    simp only [c9r9094targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 14 _ (by rfl)
  have c9r9095_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r9095targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,3),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r9095choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9095targets [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r9095choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9095targets, c9r9095choice, ?_, checked⟩
    intro S h
    simp only [c9r9095targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9088_closed
  · subst row; exact c9r9089_closed
  · subst row; exact c9r9090_closed
  · subst row; exact c9r9091_closed
  · subst row; exact c9r9092_closed
  · subst row; exact c9r9093_closed
  · subst row; exact c9r9094_closed
  · subst row; exact c9r9095_closed
theorem C9R09088G1 (row : List GridPoint) (h : row ∈ [[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9096_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r9096targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(1,3),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,4),(1,3),(1,4),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r9096choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9096targets [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r9096choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9096targets, c9r9096choice, ?_, checked⟩
    intro S h
    simp only [c9r9096targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 27 _ (by rfl)
  have c9r9097_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r9097targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,4),(1,3),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r9097choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9097targets [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r9097choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9097targets, c9r9097choice, ?_, checked⟩
    intro S h
    simp only [c9r9097targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 30 _ (by rfl)
  have c9r9098_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r9098targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,4),(1,3),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r9098choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9098targets [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r9098choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9098targets, c9r9098choice, ?_, checked⟩
    intro S h
    simp only [c9r9098targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 0 _ (by rfl)
  have c9r9099_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r9099targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,4),(1,3),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r9099choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9099targets [(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r9099choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9099targets, c9r9099choice, ?_, checked⟩
    intro S h
    simp only [c9r9099targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 2 _ (by rfl)
  have c9r9100_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r9100targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r9100choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9100targets [(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r9100choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9100targets, c9r9100choice, ?_, checked⟩
    intro S h
    simp only [c9r9100targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 10 _ (by rfl)
  have c9r9101_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r9101targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,4),(1,3),(1,4),(2,4),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r9101choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9101targets [(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r9101choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9101targets, c9r9101choice, ?_, checked⟩
    intro S h
    simp only [c9r9101targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 17 _ (by rfl)
  have c9r9102_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r9102targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,3),(1,4),(2,4),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r9102choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9102targets [(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)] c9r9102choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9102targets, c9r9102choice, ?_, checked⟩
    intro S h
    simp only [c9r9102targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 25 _ (by rfl)
  have c9r9103_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r9103targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,6)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r9103choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9103targets [(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)] c9r9103choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9103targets, c9r9103choice, ?_, checked⟩
    intro S h
    simp only [c9r9103targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9096_closed
  · subst row; exact c9r9097_closed
  · subst row; exact c9r9098_closed
  · subst row; exact c9r9099_closed
  · subst row; exact c9r9100_closed
  · subst row; exact c9r9101_closed
  · subst row; exact c9r9102_closed
  · subst row; exact c9r9103_closed
theorem C9R09088G2 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9104_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r9104targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r9104choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9104targets [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r9104choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9104targets, c9r9104choice, ?_, checked⟩
    intro S h
    simp only [c9r9104targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 13 _ (by rfl)
  have c9r9105_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)] := by
    let c9r9105targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,5)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,4),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,6)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(2,6)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,5)]]
    let c9r9105choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9105targets [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)] c9r9105choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9105targets, c9r9105choice, ?_, checked⟩
    intro S h
    simp only [c9r9105targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 19 _ (by rfl)
  have c9r9106_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r9106targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,0)],[(0,4),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r9106choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9106targets [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r9106choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9106targets, c9r9106choice, ?_, checked⟩
    intro S h
    simp only [c9r9106targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 23 _ (by rfl)
  have c9r9107_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r9107targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r9107choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9107targets [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r9107choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9107targets, c9r9107choice, ?_, checked⟩
    intro S h
    simp only [c9r9107targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 26 _ (by rfl)
  have c9r9108_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r9108targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r9108choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9108targets [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r9108choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9108targets, c9r9108choice, ?_, checked⟩
    intro S h
    simp only [c9r9108targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 28 _ (by rfl)
  have c9r9109_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r9109targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r9109choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9109targets [(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r9109choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9109targets, c9r9109choice, ?_, checked⟩
    intro S h
    simp only [c9r9109targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 30 _ (by rfl)
  have c9r9110_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r9110targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5),(3,0),(3,1)],[(0,4),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r9110choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9110targets [(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r9110choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9110targets, c9r9110choice, ?_, checked⟩
    intro S h
    simp only [c9r9110targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 7 _ (by rfl)
  have c9r9111_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r9111targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,0),(3,1),(3,2)],[(0,4),(1,4),(1,5),(1,6),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r9111choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9111targets [(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r9111choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9111targets, c9r9111choice, ?_, checked⟩
    intro S h
    simp only [c9r9111targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9104_closed
  · subst row; exact c9r9105_closed
  · subst row; exact c9r9106_closed
  · subst row; exact c9r9107_closed
  · subst row; exact c9r9108_closed
  · subst row; exact c9r9109_closed
  · subst row; exact c9r9110_closed
  · subst row; exact c9r9111_closed
theorem C9R09088G3 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9112_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9112targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(2,5),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,4),(1,5),(1,6),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9112choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9112targets [(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r9112choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9112targets, c9r9112choice, ?_, checked⟩
    intro S h
    simp only [c9r9112targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 24 _ (by rfl)
  have c9r9113_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r9113targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r9113choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9113targets [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r9113choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9113targets, c9r9113choice, ?_, checked⟩
    intro S h
    simp only [c9r9113targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 3 _ (by rfl)
  have c9r9114_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] := by
    let c9r9114targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,4),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c9r9114choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9114targets [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] c9r9114choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9114targets, c9r9114choice, ?_, checked⟩
    intro S h
    simp only [c9r9114targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 8 _ (by rfl)
  have c9r9115_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r9115targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r9115choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9115targets [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r9115choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9115targets, c9r9115choice, ?_, checked⟩
    intro S h
    simp only [c9r9115targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 12 _ (by rfl)
  have c9r9116_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r9116targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r9116choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9116targets [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r9116choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9116targets, c9r9116choice, ?_, checked⟩
    intro S h
    simp only [c9r9116targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 15 _ (by rfl)
  have c9r9117_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r9117targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r9117choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9117targets [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r9117choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9117targets, c9r9117choice, ?_, checked⟩
    intro S h
    simp only [c9r9117targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 17 _ (by rfl)
  have c9r9118_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r9118targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r9118choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9118targets [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r9118choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9118targets, c9r9118choice, ?_, checked⟩
    intro S h
    simp only [c9r9118targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 19 _ (by rfl)
  have c9r9119_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r9119targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r9119choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9119targets [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r9119choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9119targets, c9r9119choice, ?_, checked⟩
    intro S h
    simp only [c9r9119targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,true,false] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9112_closed
  · subst row; exact c9r9113_closed
  · subst row; exact c9r9114_closed
  · subst row; exact c9r9115_closed
  · subst row; exact c9r9116_closed
  · subst row; exact c9r9117_closed
  · subst row; exact c9r9118_closed
  · subst row; exact c9r9119_closed
theorem C9R09088_closed (row : List GridPoint) (h : FamilyMember row F9B004L28) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L28, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R09088G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09088G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09088G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09088G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09088G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09088G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09088G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09088G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09088G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09088G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09088G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09088G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09088G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09088G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09088G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09088G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09088G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09088G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09088G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09088G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09088G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09088G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09088G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09088G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09088G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09088G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09088G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09088G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09088G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09088G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09088G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09088G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
