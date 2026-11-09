import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03008G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3008_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)] := by
    let c9r3008targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)]]
    let c9r3008choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3008targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)] c9r3008choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3008targets, c9r3008choice, ?_, checked⟩
    intro S h
    simp only [c9r3008targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 2 _ (by rfl)
  have c9r3009_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)] := by
    let c9r3009targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)]]
    let c9r3009choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3009targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)] c9r3009choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3009targets, c9r3009choice, ?_, checked⟩
    intro S h
    simp only [c9r3009targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 5 _ (by rfl)
  have c9r3010_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)] := by
    let c9r3010targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3010choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3010targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)] c9r3010choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3010targets, c9r3010choice, ?_, checked⟩
    intro S h
    simp only [c9r3010targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 11 _ (by rfl)
  have c9r3011_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r3011targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r3011choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3011targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r3011choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3011targets, c9r3011choice, ?_, checked⟩
    intro S h
    simp only [c9r3011targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 17 _ (by rfl)
  have c9r3012_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r3012targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r3012choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3012targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r3012choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3012targets, c9r3012choice, ?_, checked⟩
    intro S h
    simp only [c9r3012targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 20 _ (by rfl)
  have c9r3013_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r3013targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r3013choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3013targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r3013choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3013targets, c9r3013choice, ?_, checked⟩
    intro S h
    simp only [c9r3013targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 22 _ (by rfl)
  have c9r3014_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r3014targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r3014choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3014targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r3014choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3014targets, c9r3014choice, ?_, checked⟩
    intro S h
    simp only [c9r3014targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 24 _ (by rfl)
  have c9r3015_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r3015targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3015choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3015targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)] c9r3015choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3015targets, c9r3015choice, ?_, checked⟩
    intro S h
    simp only [c9r3015targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3008_closed
  · subst row; exact c9r3009_closed
  · subst row; exact c9r3010_closed
  · subst row; exact c9r3011_closed
  · subst row; exact c9r3012_closed
  · subst row; exact c9r3013_closed
  · subst row; exact c9r3014_closed
  · subst row; exact c9r3015_closed
theorem C9R03008G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3016_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r3016targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r3016choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3016targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)] c9r3016choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3016targets, c9r3016choice, ?_, checked⟩
    intro S h
    simp only [c9r3016targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 2 _ (by rfl)
  have c9r3017_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r3017targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r3017choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3017targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)] c9r3017choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3017targets, c9r3017choice, ?_, checked⟩
    intro S h
    simp only [c9r3017targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 4 _ (by rfl)
  have c9r3018_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r3018targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r3018choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3018targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)] c9r3018choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3018targets, c9r3018choice, ?_, checked⟩
    intro S h
    simp only [c9r3018targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 6 _ (by rfl)
  have c9r3019_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r3019targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r3019choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3019targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] c9r3019choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3019targets, c9r3019choice, ?_, checked⟩
    intro S h
    simp only [c9r3019targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 9 _ (by rfl)
  have c9r3020_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r3020targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r3020choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3020targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)] c9r3020choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3020targets, c9r3020choice, ?_, checked⟩
    intro S h
    simp only [c9r3020targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 12 _ (by rfl)
  have c9r3021_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r3021targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r3021choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3021targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)] c9r3021choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3021targets, c9r3021choice, ?_, checked⟩
    intro S h
    simp only [c9r3021targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 15 _ (by rfl)
  have c9r3022_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r3022targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r3022choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3022targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)] c9r3022choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3022targets, c9r3022choice, ?_, checked⟩
    intro S h
    simp only [c9r3022targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 18 _ (by rfl)
  have c9r3023_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r3023targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r3023choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3023targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)] c9r3023choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3023targets, c9r3023choice, ?_, checked⟩
    intro S h
    simp only [c9r3023targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3016_closed
  · subst row; exact c9r3017_closed
  · subst row; exact c9r3018_closed
  · subst row; exact c9r3019_closed
  · subst row; exact c9r3020_closed
  · subst row; exact c9r3021_closed
  · subst row; exact c9r3022_closed
  · subst row; exact c9r3023_closed
theorem C9R03008G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3024_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r3024targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r3024choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3024targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)] c9r3024choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3024targets, c9r3024choice, ?_, checked⟩
    intro S h
    simp only [c9r3024targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 26 _ (by rfl)
  have c9r3025_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r3025targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r3025choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3025targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)] c9r3025choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3025targets, c9r3025choice, ?_, checked⟩
    intro S h
    simp only [c9r3025targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 30 _ (by rfl)
  have c9r3026_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r3026targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r3026choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3026targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)] c9r3026choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3026targets, c9r3026choice, ?_, checked⟩
    intro S h
    simp only [c9r3026targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 0 _ (by rfl)
  have c9r3027_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r3027targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r3027choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3027targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)] c9r3027choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3027targets, c9r3027choice, ?_, checked⟩
    intro S h
    simp only [c9r3027targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 2 _ (by rfl)
  have c9r3028_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r3028targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r3028choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3028targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)] c9r3028choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3028targets, c9r3028choice, ?_, checked⟩
    intro S h
    simp only [c9r3028targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 6 _ (by rfl)
  have c9r3029_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)] := by
    let c9r3029targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)]]
    let c9r3029choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3029targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)] c9r3029choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3029targets, c9r3029choice, ?_, checked⟩
    intro S h
    simp only [c9r3029targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 9 _ (by rfl)
  have c9r3030_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)] := by
    let c9r3030targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2),(6,2)]]
    let c9r3030choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3030targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)] c9r3030choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3030targets, c9r3030choice, ?_, checked⟩
    intro S h
    simp only [c9r3030targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 12 _ (by rfl)
  have c9r3031_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)] := by
    let c9r3031targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4),(5,4)]]
    let c9r3031choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3031targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)] c9r3031choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3031targets, c9r3031choice, ?_, checked⟩
    intro S h
    simp only [c9r3031targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3024_closed
  · subst row; exact c9r3025_closed
  · subst row; exact c9r3026_closed
  · subst row; exact c9r3027_closed
  · subst row; exact c9r3028_closed
  · subst row; exact c9r3029_closed
  · subst row; exact c9r3030_closed
  · subst row; exact c9r3031_closed
theorem C9R03008G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3032_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)] := by
    let c9r3032targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3),(6,3)]]
    let c9r3032choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3032targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)] c9r3032choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3032targets, c9r3032choice, ?_, checked⟩
    intro S h
    simp only [c9r3032targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 18 _ (by rfl)
  have c9r3033_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r3033targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r3033choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3033targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)] c9r3033choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3033targets, c9r3033choice, ?_, checked⟩
    intro S h
    simp only [c9r3033targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 23 _ (by rfl)
  have c9r3034_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)] := by
    let c9r3034targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)]]
    let c9r3034choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3034targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)] c9r3034choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3034targets, c9r3034choice, ?_, checked⟩
    intro S h
    simp only [c9r3034targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 27 _ (by rfl)
  have c9r3035_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)] := by
    let c9r3035targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)]]
    let c9r3035choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3035targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)] c9r3035choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3035targets, c9r3035choice, ?_, checked⟩
    intro S h
    simp only [c9r3035targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 30 _ (by rfl)
  have c9r3036_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)] := by
    let c9r3036targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)]]
    let c9r3036choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3036targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)] c9r3036choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3036targets, c9r3036choice, ?_, checked⟩
    intro S h
    simp only [c9r3036targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 0 _ (by rfl)
  have c9r3037_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)] := by
    let c9r3037targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)]]
    let c9r3037choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3037targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)] c9r3037choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3037targets, c9r3037choice, ?_, checked⟩
    intro S h
    simp only [c9r3037targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 4 _ (by rfl)
  have c9r3038_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)] := by
    let c9r3038targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2),(6,2)]]
    let c9r3038choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3038targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)] c9r3038choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3038targets, c9r3038choice, ?_, checked⟩
    intro S h
    simp only [c9r3038targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 7 _ (by rfl)
  have c9r3039_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)] := by
    let c9r3039targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3),(6,3)]]
    let c9r3039choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3039targets [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)] c9r3039choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3039targets, c9r3039choice, ?_, checked⟩
    intro S h
    simp only [c9r3039targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,false,false,true,true] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3032_closed
  · subst row; exact c9r3033_closed
  · subst row; exact c9r3034_closed
  · subst row; exact c9r3035_closed
  · subst row; exact c9r3036_closed
  · subst row; exact c9r3037_closed
  · subst row; exact c9r3038_closed
  · subst row; exact c9r3039_closed
theorem C9R03008_closed (row : List GridPoint) (h : FamilyMember row F9B001L30) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L30, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03008G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03008G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03008G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03008G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03008G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03008G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03008G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03008G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03008G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03008G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03008G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03008G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03008G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03008G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03008G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03008G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03008G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03008G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03008G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03008G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03008G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03008G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03008G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03008G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03008G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03008G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03008G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03008G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03008G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03008G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03008G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03008G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
