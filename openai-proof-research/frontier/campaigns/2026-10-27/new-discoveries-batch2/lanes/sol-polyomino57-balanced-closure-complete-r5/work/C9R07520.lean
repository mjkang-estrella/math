import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R07520G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7520_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)] := by
    let c9r7520targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)]]
    let c9r7520choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7520targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)] c9r7520choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7520targets, c9r7520choice, ?_, checked⟩
    intro S h
    simp only [c9r7520targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 7 _ (by rfl)
  have c9r7521_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r7521targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r7521choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7521targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)] c9r7521choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7521targets, c9r7521choice, ?_, checked⟩
    intro S h
    simp only [c9r7521targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 10 _ (by rfl)
  have c9r7522_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r7522targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r7522choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7522targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)] c9r7522choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7522targets, c9r7522choice, ?_, checked⟩
    intro S h
    simp only [c9r7522targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 12 _ (by rfl)
  have c9r7523_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r7523targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r7523choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7523targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)] c9r7523choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7523targets, c9r7523choice, ?_, checked⟩
    intro S h
    simp only [c9r7523targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 14 _ (by rfl)
  have c9r7524_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)] := by
    let c9r7524targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3),(3,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,4)]]
    let c9r7524choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7524targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)] c9r7524choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7524targets, c9r7524choice, ?_, checked⟩
    intro S h
    simp only [c9r7524targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 19 _ (by rfl)
  have c9r7525_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)] := by
    let c9r7525targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(4,0)]]
    let c9r7525choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7525targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)] c9r7525choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7525targets, c9r7525choice, ?_, checked⟩
    intro S h
    simp only [c9r7525targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 22 _ (by rfl)
  have c9r7526_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)] := by
    let c9r7526targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(4,1)]]
    let c9r7526choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7526targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)] c9r7526choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7526targets, c9r7526choice, ?_, checked⟩
    intro S h
    simp only [c9r7526targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 25 _ (by rfl)
  have c9r7527_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)] := by
    let c9r7527targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3),(4,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3),(4,3)]]
    let c9r7527choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7527targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)] c9r7527choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7527targets, c9r7527choice, ?_, checked⟩
    intro S h
    simp only [c9r7527targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7520_closed
  · subst row; exact c9r7521_closed
  · subst row; exact c9r7522_closed
  · subst row; exact c9r7523_closed
  · subst row; exact c9r7524_closed
  · subst row; exact c9r7525_closed
  · subst row; exact c9r7526_closed
  · subst row; exact c9r7527_closed
theorem C9R07520G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7528_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)] := by
    let c9r7528targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4),(3,5)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(2,5)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(2,6)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(2,6)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,5)]]
    let c9r7528choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7528targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)] c9r7528choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7528targets, c9r7528choice, ?_, checked⟩
    intro S h
    simp only [c9r7528targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 1 _ (by rfl)
  have c9r7529_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)] := by
    let c9r7529targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(4,0)]]
    let c9r7529choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7529targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)] c9r7529choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7529targets, c9r7529choice, ?_, checked⟩
    intro S h
    simp only [c9r7529targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 4 _ (by rfl)
  have c9r7530_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)] := by
    let c9r7530targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(4,1)]]
    let c9r7530choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7530targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)] c9r7530choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7530targets, c9r7530choice, ?_, checked⟩
    intro S h
    simp only [c9r7530targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 7 _ (by rfl)
  have c9r7531_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)] := by
    let c9r7531targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4),(4,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4),(3,4)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5),(3,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,3),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(3,5)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4),(4,4)]]
    let c9r7531choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7531targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)] c9r7531choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7531targets, c9r7531choice, ?_, checked⟩
    intro S h
    simp only [c9r7531targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 10 _ (by rfl)
  have c9r7532_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)] := by
    let c9r7532targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c9r7532choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7532targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)] c9r7532choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7532targets, c9r7532choice, ?_, checked⟩
    intro S h
    simp only [c9r7532targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 13 _ (by rfl)
  have c9r7533_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)] := by
    let c9r7533targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0),(4,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(4,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c9r7533choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7533targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)] c9r7533choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7533targets, c9r7533choice, ?_, checked⟩
    intro S h
    simp only [c9r7533targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 15 _ (by rfl)
  have c9r7534_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)] := by
    let c9r7534targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c9r7534choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7534targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)] c9r7534choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7534targets, c9r7534choice, ?_, checked⟩
    intro S h
    simp only [c9r7534targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 18 _ (by rfl)
  have c9r7535_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)] := by
    let c9r7535targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1),(4,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c9r7535choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7535targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)] c9r7535choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7535targets, c9r7535choice, ?_, checked⟩
    intro S h
    simp only [c9r7535targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7528_closed
  · subst row; exact c9r7529_closed
  · subst row; exact c9r7530_closed
  · subst row; exact c9r7531_closed
  · subst row; exact c9r7532_closed
  · subst row; exact c9r7533_closed
  · subst row; exact c9r7534_closed
  · subst row; exact c9r7535_closed
theorem C9R07520G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7536_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r7536targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r7536choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7536targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)] c9r7536choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7536targets, c9r7536choice, ?_, checked⟩
    intro S h
    simp only [c9r7536targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 27 _ (by rfl)
  have c9r7537_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)] := by
    let c9r7537targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(4,1)]]
    let c9r7537choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7537targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)] c9r7537choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7537targets, c9r7537choice, ?_, checked⟩
    intro S h
    simp only [c9r7537targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 1 _ (by rfl)
  have c9r7538_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)] := by
    let c9r7538targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1),(3,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1),(4,1)]]
    let c9r7538choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7538targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)] c9r7538choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7538targets, c9r7538choice, ?_, checked⟩
    intro S h
    simp only [c9r7538targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 7 _ (by rfl)
  have c9r7539_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)] := by
    let c9r7539targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c9r7539choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7539targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)] c9r7539choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7539targets, c9r7539choice, ?_, checked⟩
    intro S h
    simp only [c9r7539targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 12 _ (by rfl)
  have c9r7540_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)] := by
    let c9r7540targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c9r7540choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7540targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)] c9r7540choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7540targets, c9r7540choice, ?_, checked⟩
    intro S h
    simp only [c9r7540targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 14 _ (by rfl)
  have c9r7541_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)] := by
    let c9r7541targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c9r7541choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7541targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)] c9r7541choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7541targets, c9r7541choice, ?_, checked⟩
    intro S h
    simp only [c9r7541targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 16 _ (by rfl)
  have c9r7542_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)] := by
    let c9r7542targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c9r7542choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7542targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)] c9r7542choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7542targets, c9r7542choice, ?_, checked⟩
    intro S h
    simp only [c9r7542targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 20 _ (by rfl)
  have c9r7543_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r7543targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r7543choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7543targets [(0,2),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)] c9r7543choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7543targets, c9r7543choice, ?_, checked⟩
    intro S h
    simp only [c9r7543targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,false] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7536_closed
  · subst row; exact c9r7537_closed
  · subst row; exact c9r7538_closed
  · subst row; exact c9r7539_closed
  · subst row; exact c9r7540_closed
  · subst row; exact c9r7541_closed
  · subst row; exact c9r7542_closed
  · subst row; exact c9r7543_closed
theorem C9R07520G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7544_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r7544targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r7544choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7544targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r7544choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7544targets, c9r7544choice, ?_, checked⟩
    intro S h
    simp only [c9r7544targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 5 _ (by rfl)
  have c9r7545_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r7545targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r7545choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7545targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r7545choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7545targets, c9r7545choice, ?_, checked⟩
    intro S h
    simp only [c9r7545targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 9 _ (by rfl)
  have c9r7546_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r7546targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r7546choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))))))
    have checked : successorFastRowCheck c9r7546targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r7546choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7546targets, c9r7546choice, ?_, checked⟩
    intro S h
    simp only [c9r7546targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 12 _ (by rfl)
  have c9r7547_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r7547targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r7547choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))))))
    have checked : successorFastRowCheck c9r7547targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r7547choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7547targets, c9r7547choice, ?_, checked⟩
    intro S h
    simp only [c9r7547targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 14 _ (by rfl)
  have c9r7548_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r7548targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r7548choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7548targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r7548choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7548targets, c9r7548choice, ?_, checked⟩
    intro S h
    simp only [c9r7548targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 16 _ (by rfl)
  have c9r7549_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r7549targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r7549choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))))))
    have checked : successorFastRowCheck c9r7549targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)] c9r7549choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7549targets, c9r7549choice, ?_, checked⟩
    intro S h
    simp only [c9r7549targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 19 _ (by rfl)
  have c9r7550_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c9r7550targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c9r7550choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7550targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)] c9r7550choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7550targets, c9r7550choice, ?_, checked⟩
    intro S h
    simp only [c9r7550targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 22 _ (by rfl)
  have c9r7551_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c9r7551targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c9r7551choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7551targets [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)] c9r7551choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7551targets, c9r7551choice, ?_, checked⟩
    intro S h
    simp only [c9r7551targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,false,true,true,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7544_closed
  · subst row; exact c9r7545_closed
  · subst row; exact c9r7546_closed
  · subst row; exact c9r7547_closed
  · subst row; exact c9r7548_closed
  · subst row; exact c9r7549_closed
  · subst row; exact c9r7550_closed
  · subst row; exact c9r7551_closed
theorem C9R07520_closed (row : List GridPoint) (h : FamilyMember row F9B003L43) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L43, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R07520G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07520G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07520G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07520G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07520G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07520G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07520G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07520G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07520G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07520G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07520G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07520G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07520G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07520G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07520G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07520G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07520G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07520G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07520G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07520G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07520G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07520G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07520G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07520G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07520G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07520G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07520G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07520G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07520G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07520G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07520G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07520G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
