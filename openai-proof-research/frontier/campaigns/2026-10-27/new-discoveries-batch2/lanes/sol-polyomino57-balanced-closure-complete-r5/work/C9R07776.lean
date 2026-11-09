import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R07776G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7776_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r7776targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r7776choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7776targets [(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r7776choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7776targets, c9r7776choice, ?_, checked⟩
    intro S h
    simp only [c9r7776targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 7 _ (by rfl)
  have c9r7777_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r7777targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r7777choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7777targets [(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r7777choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7777targets, c9r7777choice, ?_, checked⟩
    intro S h
    simp only [c9r7777targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 14 _ (by rfl)
  have c9r7778_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r7778targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r7778choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7778targets [(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r7778choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7778targets, c9r7778choice, ?_, checked⟩
    intro S h
    simp only [c9r7778targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 17 _ (by rfl)
  have c9r7779_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r7779targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r7779choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7779targets [(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r7779choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7779targets, c9r7779choice, ?_, checked⟩
    intro S h
    simp only [c9r7779targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 19 _ (by rfl)
  have c9r7780_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r7780targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r7780choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7780targets [(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r7780choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7780targets, c9r7780choice, ?_, checked⟩
    intro S h
    simp only [c9r7780targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 21 _ (by rfl)
  have c9r7781_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r7781targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r7781choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7781targets [(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)] c9r7781choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7781targets, c9r7781choice, ?_, checked⟩
    intro S h
    simp only [c9r7781targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 26 _ (by rfl)
  have c9r7782_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r7782targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r7782choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r7782targets [(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)] c9r7782choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7782targets, c9r7782choice, ?_, checked⟩
    intro S h
    simp only [c9r7782targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 0 _ (by rfl)
  have c9r7783_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)] := by
    let c9r7783targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,2),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2)],[(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,6)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,2)]]
    let c9r7783choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r7783targets [(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)] c9r7783choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7783targets, c9r7783choice, ?_, checked⟩
    intro S h
    simp only [c9r7783targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7776_closed
  · subst row; exact c9r7777_closed
  · subst row; exact c9r7778_closed
  · subst row; exact c9r7779_closed
  · subst row; exact c9r7780_closed
  · subst row; exact c9r7781_closed
  · subst row; exact c9r7782_closed
  · subst row; exact c9r7783_closed
theorem C9R07776G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7784_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r7784targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r7784choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7784targets [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)] c9r7784choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7784targets, c9r7784choice, ?_, checked⟩
    intro S h
    simp only [c9r7784targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 18 _ (by rfl)
  have c9r7785_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)] := by
    let c9r7785targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,4)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,4)]]
    let c9r7785choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7785targets [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)] c9r7785choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7785targets, c9r7785choice, ?_, checked⟩
    intro S h
    simp only [c9r7785targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 23 _ (by rfl)
  have c9r7786_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)] := by
    let c9r7786targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,5)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,5)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,6)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(2,6)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,5)]]
    let c9r7786choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7786targets [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)] c9r7786choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7786targets, c9r7786choice, ?_, checked⟩
    intro S h
    simp only [c9r7786targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 28 _ (by rfl)
  have c9r7787_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r7787targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,0)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r7787choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7787targets [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)] c9r7787choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7787targets, c9r7787choice, ?_, checked⟩
    intro S h
    simp only [c9r7787targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 31 _ (by rfl)
  have c9r7788_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r7788targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r7788choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7788targets [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)] c9r7788choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7788targets, c9r7788choice, ?_, checked⟩
    intro S h
    simp only [c9r7788targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 1 _ (by rfl)
  have c9r7789_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r7789targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r7789choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7789targets [(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)] c9r7789choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7789targets, c9r7789choice, ?_, checked⟩
    intro S h
    simp only [c9r7789targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 3 _ (by rfl)
  have c9r7790_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r7790targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r7790choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7790targets [(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)] c9r7790choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7790targets, c9r7790choice, ?_, checked⟩
    intro S h
    simp only [c9r7790targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 10 _ (by rfl)
  have c9r7791_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r7791targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r7791choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r7791targets [(0,2),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)] c9r7791choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7791targets, c9r7791choice, ?_, checked⟩
    intro S h
    simp only [c9r7791targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 18 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7784_closed
  · subst row; exact c9r7785_closed
  · subst row; exact c9r7786_closed
  · subst row; exact c9r7787_closed
  · subst row; exact c9r7788_closed
  · subst row; exact c9r7789_closed
  · subst row; exact c9r7790_closed
  · subst row; exact c9r7791_closed
theorem C9R07776G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7792_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r7792targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r7792choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7792targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r7792choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7792targets, c9r7792choice, ?_, checked⟩
    intro S h
    simp only [c9r7792targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 27 _ (by rfl)
  have c9r7793_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r7793targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r7793choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7793targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r7793choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7793targets, c9r7793choice, ?_, checked⟩
    intro S h
    simp only [c9r7793targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 31 _ (by rfl)
  have c9r7794_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r7794targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r7794choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7794targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r7794choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7794targets, c9r7794choice, ?_, checked⟩
    intro S h
    simp only [c9r7794targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 2 _ (by rfl)
  have c9r7795_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r7795targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r7795choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7795targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r7795choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7795targets, c9r7795choice, ?_, checked⟩
    intro S h
    simp only [c9r7795targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 4 _ (by rfl)
  have c9r7796_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r7796targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r7796choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7796targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r7796choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7796targets, c9r7796choice, ?_, checked⟩
    intro S h
    simp only [c9r7796targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 6 _ (by rfl)
  have c9r7797_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)] := by
    let c9r7797targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(3,5)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(2,6)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(2,6)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,5)]]
    let c9r7797choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7797targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)] c9r7797choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7797targets, c9r7797choice, ?_, checked⟩
    intro S h
    simp only [c9r7797targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 12 _ (by rfl)
  have c9r7798_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)] := by
    let c9r7798targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,0)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,0)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(4,0)]]
    let c9r7798choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7798targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)] c9r7798choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7798targets, c9r7798choice, ?_, checked⟩
    intro S h
    simp only [c9r7798targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 16 _ (by rfl)
  have c9r7799_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)] := by
    let c9r7799targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(4,1)]]
    let c9r7799choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7799targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)] c9r7799choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7799targets, c9r7799choice, ?_, checked⟩
    intro S h
    simp only [c9r7799targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7792_closed
  · subst row; exact c9r7793_closed
  · subst row; exact c9r7794_closed
  · subst row; exact c9r7795_closed
  · subst row; exact c9r7796_closed
  · subst row; exact c9r7797_closed
  · subst row; exact c9r7798_closed
  · subst row; exact c9r7799_closed
theorem C9R07776G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7800_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)] := by
    let c9r7800targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(4,2)]]
    let c9r7800choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7800targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)] c9r7800choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7800targets, c9r7800choice, ?_, checked⟩
    intro S h
    simp only [c9r7800targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 22 _ (by rfl)
  have c9r7801_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)] := by
    let c9r7801targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4),(4,4)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5),(3,5)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,3),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4),(3,5)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4),(4,4)]]
    let c9r7801choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7801targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)] c9r7801choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7801targets, c9r7801choice, ?_, checked⟩
    intro S h
    simp only [c9r7801targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 25 _ (by rfl)
  have c9r7802_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r7802targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r7802choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7802targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)] c9r7802choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7802targets, c9r7802choice, ?_, checked⟩
    intro S h
    simp only [c9r7802targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 28 _ (by rfl)
  have c9r7803_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c9r7803targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c9r7803choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7803targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)] c9r7803choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7803targets, c9r7803choice, ?_, checked⟩
    intro S h
    simp only [c9r7803targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 31 _ (by rfl)
  have c9r7804_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c9r7804targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0),(4,0)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c9r7804choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7804targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)] c9r7804choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7804targets, c9r7804choice, ?_, checked⟩
    intro S h
    simp only [c9r7804targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 1 _ (by rfl)
  have c9r7805_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c9r7805targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c9r7805choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7805targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)] c9r7805choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7805targets, c9r7805choice, ?_, checked⟩
    intro S h
    simp only [c9r7805targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 4 _ (by rfl)
  have c9r7806_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c9r7806targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c9r7806choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7806targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)] c9r7806choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7806targets, c9r7806choice, ?_, checked⟩
    intro S h
    simp only [c9r7806targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 7 _ (by rfl)
  have c9r7807_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c9r7807targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c9r7807choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7807targets [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)] c9r7807choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7807targets, c9r7807choice, ?_, checked⟩
    intro S h
    simp only [c9r7807targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7800_closed
  · subst row; exact c9r7801_closed
  · subst row; exact c9r7802_closed
  · subst row; exact c9r7803_closed
  · subst row; exact c9r7804_closed
  · subst row; exact c9r7805_closed
  · subst row; exact c9r7806_closed
  · subst row; exact c9r7807_closed
theorem C9R07776_closed (row : List GridPoint) (h : FamilyMember row F9B003L51) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L51, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R07776G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07776G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07776G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07776G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07776G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07776G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07776G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07776G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07776G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07776G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07776G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07776G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07776G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07776G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07776G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07776G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07776G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07776G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07776G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07776G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07776G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07776G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07776G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07776G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07776G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07776G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07776G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07776G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07776G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07776G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07776G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07776G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
