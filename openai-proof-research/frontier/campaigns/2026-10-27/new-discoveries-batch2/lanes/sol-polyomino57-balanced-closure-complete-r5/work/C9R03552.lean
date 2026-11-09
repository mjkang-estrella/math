import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03552G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3552_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r3552targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r3552choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3552targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)] c9r3552choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3552targets, c9r3552choice, ?_, checked⟩
    intro S h
    simp only [c9r3552targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 15 _ (by rfl)
  have c9r3553_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r3553targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r3553choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3553targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] c9r3553choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3553targets, c9r3553choice, ?_, checked⟩
    intro S h
    simp only [c9r3553targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 18 _ (by rfl)
  have c9r3554_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r3554targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r3554choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3554targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)] c9r3554choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3554targets, c9r3554choice, ?_, checked⟩
    intro S h
    simp only [c9r3554targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 21 _ (by rfl)
  have c9r3555_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r3555targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r3555choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3555targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)] c9r3555choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3555targets, c9r3555choice, ?_, checked⟩
    intro S h
    simp only [c9r3555targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 24 _ (by rfl)
  have c9r3556_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r3556targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r3556choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3556targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)] c9r3556choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3556targets, c9r3556choice, ?_, checked⟩
    intro S h
    simp only [c9r3556targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 29 _ (by rfl)
  have c9r3557_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r3557targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r3557choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3557targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)] c9r3557choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3557targets, c9r3557choice, ?_, checked⟩
    intro S h
    simp only [c9r3557targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 1 _ (by rfl)
  have c9r3558_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r3558targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r3558choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3558targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)] c9r3558choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3558targets, c9r3558choice, ?_, checked⟩
    intro S h
    simp only [c9r3558targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 3 _ (by rfl)
  have c9r3559_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r3559targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r3559choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3559targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)] c9r3559choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3559targets, c9r3559choice, ?_, checked⟩
    intro S h
    simp only [c9r3559targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3552_closed
  · subst row; exact c9r3553_closed
  · subst row; exact c9r3554_closed
  · subst row; exact c9r3555_closed
  · subst row; exact c9r3556_closed
  · subst row; exact c9r3557_closed
  · subst row; exact c9r3558_closed
  · subst row; exact c9r3559_closed
theorem C9R03552G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3560_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r3560targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r3560choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3560targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)] c9r3560choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3560targets, c9r3560choice, ?_, checked⟩
    intro S h
    simp only [c9r3560targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 9 _ (by rfl)
  have c9r3561_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)] := by
    let c9r3561targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)]]
    let c9r3561choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3561targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)] c9r3561choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3561targets, c9r3561choice, ?_, checked⟩
    intro S h
    simp only [c9r3561targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 12 _ (by rfl)
  have c9r3562_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)] := by
    let c9r3562targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(6,2)]]
    let c9r3562choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3562targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)] c9r3562choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3562targets, c9r3562choice, ?_, checked⟩
    intro S h
    simp only [c9r3562targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 15 _ (by rfl)
  have c9r3563_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)] := by
    let c9r3563targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,4)]]
    let c9r3563choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3563targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)] c9r3563choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3563targets, c9r3563choice, ?_, checked⟩
    intro S h
    simp only [c9r3563targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 18 _ (by rfl)
  have c9r3564_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)] := by
    let c9r3564targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(6,3)]]
    let c9r3564choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3564targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)] c9r3564choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3564targets, c9r3564choice, ?_, checked⟩
    intro S h
    simp only [c9r3564targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 21 _ (by rfl)
  have c9r3565_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r3565targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r3565choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3565targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)] c9r3565choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3565targets, c9r3565choice, ?_, checked⟩
    intro S h
    simp only [c9r3565targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 26 _ (by rfl)
  have c9r3566_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)] := by
    let c9r3566targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)]]
    let c9r3566choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3566targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)] c9r3566choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3566targets, c9r3566choice, ?_, checked⟩
    intro S h
    simp only [c9r3566targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 30 _ (by rfl)
  have c9r3567_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)] := by
    let c9r3567targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)]]
    let c9r3567choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3567targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)] c9r3567choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3567targets, c9r3567choice, ?_, checked⟩
    intro S h
    simp only [c9r3567targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3560_closed
  · subst row; exact c9r3561_closed
  · subst row; exact c9r3562_closed
  · subst row; exact c9r3563_closed
  · subst row; exact c9r3564_closed
  · subst row; exact c9r3565_closed
  · subst row; exact c9r3566_closed
  · subst row; exact c9r3567_closed
theorem C9R03552G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3568_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)] := by
    let c9r3568targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)]]
    let c9r3568choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3568targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)] c9r3568choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3568targets, c9r3568choice, ?_, checked⟩
    intro S h
    simp only [c9r3568targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 3 _ (by rfl)
  have c9r3569_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)] := by
    let c9r3569targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)]]
    let c9r3569choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3569targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)] c9r3569choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3569targets, c9r3569choice, ?_, checked⟩
    intro S h
    simp only [c9r3569targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 7 _ (by rfl)
  have c9r3570_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)] := by
    let c9r3570targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(6,2)]]
    let c9r3570choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3570targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)] c9r3570choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3570targets, c9r3570choice, ?_, checked⟩
    intro S h
    simp only [c9r3570targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 10 _ (by rfl)
  have c9r3571_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)] := by
    let c9r3571targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(6,3)]]
    let c9r3571choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3571targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)] c9r3571choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3571targets, c9r3571choice, ?_, checked⟩
    intro S h
    simp only [c9r3571targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 12 _ (by rfl)
  have c9r3572_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)] := by
    let c9r3572targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,2)]]
    let c9r3572choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3572targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)] c9r3572choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3572targets, c9r3572choice, ?_, checked⟩
    intro S h
    simp only [c9r3572targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 16 _ (by rfl)
  have c9r3573_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)] := by
    let c9r3573targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,3)]]
    let c9r3573choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3573targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)] c9r3573choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3573targets, c9r3573choice, ?_, checked⟩
    intro S h
    simp only [c9r3573targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 19 _ (by rfl)
  have c9r3574_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)] := by
    let c9r3574targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2),(7,2)]]
    let c9r3574choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3574targets [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)] c9r3574choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3574targets, c9r3574choice, ?_, checked⟩
    intro S h
    simp only [c9r3574targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 22 _ (by rfl)
  have c9r3575_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)] := by
    let c9r3575targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,3)]]
    let c9r3575choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3575targets [(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)] c9r3575choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3575targets, c9r3575choice, ?_, checked⟩
    intro S h
    simp only [c9r3575targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3568_closed
  · subst row; exact c9r3569_closed
  · subst row; exact c9r3570_closed
  · subst row; exact c9r3571_closed
  · subst row; exact c9r3572_closed
  · subst row; exact c9r3573_closed
  · subst row; exact c9r3574_closed
  · subst row; exact c9r3575_closed
theorem C9R03552G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3576_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r3576targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r3576choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3576targets [(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r3576choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3576targets, c9r3576choice, ?_, checked⟩
    intro S h
    simp only [c9r3576targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 1 _ (by rfl)
  have c9r3577_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r3577targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3577choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3577targets [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)] c9r3577choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3577targets, c9r3577choice, ?_, checked⟩
    intro S h
    simp only [c9r3577targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 6 _ (by rfl)
  have c9r3578_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r3578targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r3578choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3578targets [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)] c9r3578choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3578targets, c9r3578choice, ?_, checked⟩
    intro S h
    simp only [c9r3578targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 10 _ (by rfl)
  have c9r3579_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r3579targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r3579choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3579targets [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)] c9r3579choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3579targets, c9r3579choice, ?_, checked⟩
    intro S h
    simp only [c9r3579targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 12 _ (by rfl)
  have c9r3580_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r3580targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r3580choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3580targets [(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)] c9r3580choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3580targets, c9r3580choice, ?_, checked⟩
    intro S h
    simp only [c9r3580targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 14 _ (by rfl)
  have c9r3581_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r3581targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,4),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,4),(2,5),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3581choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3581targets [(0,0),(1,0),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)] c9r3581choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3581targets, c9r3581choice, ?_, checked⟩
    intro S h
    simp only [c9r3581targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 22 _ (by rfl)
  have c9r3582_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r3582targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3582choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3582targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r3582choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3582targets, c9r3582choice, ?_, checked⟩
    intro S h
    simp only [c9r3582targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 29 _ (by rfl)
  have c9r3583_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r3583targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r3583choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3583targets [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r3583choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3583targets, c9r3583choice, ?_, checked⟩
    intro S h
    simp only [c9r3583targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3576_closed
  · subst row; exact c9r3577_closed
  · subst row; exact c9r3578_closed
  · subst row; exact c9r3579_closed
  · subst row; exact c9r3580_closed
  · subst row; exact c9r3581_closed
  · subst row; exact c9r3582_closed
  · subst row; exact c9r3583_closed
theorem C9R03552_closed (row : List GridPoint) (h : FamilyMember row F9B001L47) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L47, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03552G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03552G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03552G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03552G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03552G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03552G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03552G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03552G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03552G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03552G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03552G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03552G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03552G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03552G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03552G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03552G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03552G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03552G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03552G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03552G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03552G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03552G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03552G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03552G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03552G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03552G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03552G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03552G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03552G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03552G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03552G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03552G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
