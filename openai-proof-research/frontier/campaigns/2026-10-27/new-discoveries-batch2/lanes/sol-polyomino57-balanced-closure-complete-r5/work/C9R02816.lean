import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R02816G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2816_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r2816targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r2816choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r2816targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)] c9r2816choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2816targets, c9r2816choice, ?_, checked⟩
    intro S h
    simp only [c9r2816targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 17 _ (by rfl)
  have c9r2817_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)] := by
    let c9r2817targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c9r2817choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r2817targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)] c9r2817choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2817targets, c9r2817choice, ?_, checked⟩
    intro S h
    simp only [c9r2817targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 21 _ (by rfl)
  have c9r2818_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)] := by
    let c9r2818targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c9r2818choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r2818targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)] c9r2818choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2818targets, c9r2818choice, ?_, checked⟩
    intro S h
    simp only [c9r2818targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 24 _ (by rfl)
  have c9r2819_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)] := by
    let c9r2819targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c9r2819choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2819targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)] c9r2819choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2819targets, c9r2819choice, ?_, checked⟩
    intro S h
    simp only [c9r2819targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 27 _ (by rfl)
  have c9r2820_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)] := by
    let c9r2820targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c9r2820choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r2820targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)] c9r2820choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2820targets, c9r2820choice, ?_, checked⟩
    intro S h
    simp only [c9r2820targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 30 _ (by rfl)
  have c9r2821_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)] := by
    let c9r2821targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c9r2821choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2821targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)] c9r2821choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2821targets, c9r2821choice, ?_, checked⟩
    intro S h
    simp only [c9r2821targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 1 _ (by rfl)
  have c9r2822_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r2822targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r2822choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2822targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)] c9r2822choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2822targets, c9r2822choice, ?_, checked⟩
    intro S h
    simp only [c9r2822targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 6 _ (by rfl)
  have c9r2823_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)] := by
    let c9r2823targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c9r2823choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2823targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)] c9r2823choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2823targets, c9r2823choice, ?_, checked⟩
    intro S h
    simp only [c9r2823targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2816_closed
  · subst row; exact c9r2817_closed
  · subst row; exact c9r2818_closed
  · subst row; exact c9r2819_closed
  · subst row; exact c9r2820_closed
  · subst row; exact c9r2821_closed
  · subst row; exact c9r2822_closed
  · subst row; exact c9r2823_closed
theorem C9R02816G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2824_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)] := by
    let c9r2824targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c9r2824choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2824targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)] c9r2824choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2824targets, c9r2824choice, ?_, checked⟩
    intro S h
    simp only [c9r2824targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 13 _ (by rfl)
  have c9r2825_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)] := by
    let c9r2825targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c9r2825choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2825targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)] c9r2825choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2825targets, c9r2825choice, ?_, checked⟩
    intro S h
    simp only [c9r2825targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 15 _ (by rfl)
  have c9r2826_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)] := by
    let c9r2826targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c9r2826choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2826targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)] c9r2826choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2826targets, c9r2826choice, ?_, checked⟩
    intro S h
    simp only [c9r2826targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 19 _ (by rfl)
  have c9r2827_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)] := by
    let c9r2827targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c9r2827choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2827targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)] c9r2827choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2827targets, c9r2827choice, ?_, checked⟩
    intro S h
    simp only [c9r2827targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 22 _ (by rfl)
  have c9r2828_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)] := by
    let c9r2828targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c9r2828choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2828targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)] c9r2828choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2828targets, c9r2828choice, ?_, checked⟩
    intro S h
    simp only [c9r2828targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 24 _ (by rfl)
  have c9r2829_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)] := by
    let c9r2829targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c9r2829choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2829targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)] c9r2829choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2829targets, c9r2829choice, ?_, checked⟩
    intro S h
    simp only [c9r2829targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 28 _ (by rfl)
  have c9r2830_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)] := by
    let c9r2830targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c9r2830choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2830targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)] c9r2830choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2830targets, c9r2830choice, ?_, checked⟩
    intro S h
    simp only [c9r2830targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 31 _ (by rfl)
  have c9r2831_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)] := by
    let c9r2831targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c9r2831choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r2831targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)] c9r2831choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2831targets, c9r2831choice, ?_, checked⟩
    intro S h
    simp only [c9r2831targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2824_closed
  · subst row; exact c9r2825_closed
  · subst row; exact c9r2826_closed
  · subst row; exact c9r2827_closed
  · subst row; exact c9r2828_closed
  · subst row; exact c9r2829_closed
  · subst row; exact c9r2830_closed
  · subst row; exact c9r2831_closed
theorem C9R02816G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2832_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r2832targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r2832choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r2832targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)] c9r2832choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2832targets, c9r2832choice, ?_, checked⟩
    intro S h
    simp only [c9r2832targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 7 _ (by rfl)
  have c9r2833_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)] := by
    let c9r2833targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c9r2833choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2833targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)] c9r2833choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2833targets, c9r2833choice, ?_, checked⟩
    intro S h
    simp only [c9r2833targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 11 _ (by rfl)
  have c9r2834_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)] := by
    let c9r2834targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c9r2834choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2834targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)] c9r2834choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2834targets, c9r2834choice, ?_, checked⟩
    intro S h
    simp only [c9r2834targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 13 _ (by rfl)
  have c9r2835_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r2835targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r2835choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2835targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)] c9r2835choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2835targets, c9r2835choice, ?_, checked⟩
    intro S h
    simp only [c9r2835targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 15 _ (by rfl)
  have c9r2836_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)] := by
    let c9r2836targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3)]]
    let c9r2836choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2836targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)] c9r2836choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2836targets, c9r2836choice, ?_, checked⟩
    intro S h
    simp only [c9r2836targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 19 _ (by rfl)
  have c9r2837_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)] := by
    let c9r2837targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4)]]
    let c9r2837choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2837targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)] c9r2837choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2837targets, c9r2837choice, ?_, checked⟩
    intro S h
    simp only [c9r2837targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 22 _ (by rfl)
  have c9r2838_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)] := by
    let c9r2838targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3)]]
    let c9r2838choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2838targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)] c9r2838choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2838targets, c9r2838choice, ?_, checked⟩
    intro S h
    simp only [c9r2838targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 25 _ (by rfl)
  have c9r2839_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)] := by
    let c9r2839targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5)]]
    let c9r2839choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r2839targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)] c9r2839choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2839targets, c9r2839choice, ?_, checked⟩
    intro S h
    simp only [c9r2839targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2832_closed
  · subst row; exact c9r2833_closed
  · subst row; exact c9r2834_closed
  · subst row; exact c9r2835_closed
  · subst row; exact c9r2836_closed
  · subst row; exact c9r2837_closed
  · subst row; exact c9r2838_closed
  · subst row; exact c9r2839_closed
theorem C9R02816G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2840_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)] := by
    let c9r2840targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4)]]
    let c9r2840choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2840targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)] c9r2840choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2840targets, c9r2840choice, ?_, checked⟩
    intro S h
    simp only [c9r2840targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 31 _ (by rfl)
  have c9r2841_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r2841targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r2841choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2841targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)] c9r2841choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2841targets, c9r2841choice, ?_, checked⟩
    intro S h
    simp only [c9r2841targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 5 _ (by rfl)
  have c9r2842_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)] := by
    let c9r2842targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4)]]
    let c9r2842choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2842targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)] c9r2842choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2842targets, c9r2842choice, ?_, checked⟩
    intro S h
    simp only [c9r2842targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 9 _ (by rfl)
  have c9r2843_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)] := by
    let c9r2843targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)]]
    let c9r2843choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2843targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)] c9r2843choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2843targets, c9r2843choice, ?_, checked⟩
    intro S h
    simp only [c9r2843targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 12 _ (by rfl)
  have c9r2844_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)] := by
    let c9r2844targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)]]
    let c9r2844choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2844targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)] c9r2844choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2844targets, c9r2844choice, ?_, checked⟩
    intro S h
    simp only [c9r2844targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 14 _ (by rfl)
  have c9r2845_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)] := by
    let c9r2845targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)]]
    let c9r2845choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r2845targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)] c9r2845choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2845targets, c9r2845choice, ?_, checked⟩
    intro S h
    simp only [c9r2845targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 18 _ (by rfl)
  have c9r2846_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)] := by
    let c9r2846targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(5,3)]]
    let c9r2846choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2846targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)] c9r2846choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2846targets, c9r2846choice, ?_, checked⟩
    intro S h
    simp only [c9r2846targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 21 _ (by rfl)
  have c9r2847_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)] := by
    let c9r2847targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4),(5,4)]]
    let c9r2847choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r2847targets [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)] c9r2847choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2847targets, c9r2847choice, ?_, checked⟩
    intro S h
    simp only [c9r2847targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,true,true,true,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2840_closed
  · subst row; exact c9r2841_closed
  · subst row; exact c9r2842_closed
  · subst row; exact c9r2843_closed
  · subst row; exact c9r2844_closed
  · subst row; exact c9r2845_closed
  · subst row; exact c9r2846_closed
  · subst row; exact c9r2847_closed
theorem C9R02816_closed (row : List GridPoint) (h : FamilyMember row F9B001L24) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L24, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R02816G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02816G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02816G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02816G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02816G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02816G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02816G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02816G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02816G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02816G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02816G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02816G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02816G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02816G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02816G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02816G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02816G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02816G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02816G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02816G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02816G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02816G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02816G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02816G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02816G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02816G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02816G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02816G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02816G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02816G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02816G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02816G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
