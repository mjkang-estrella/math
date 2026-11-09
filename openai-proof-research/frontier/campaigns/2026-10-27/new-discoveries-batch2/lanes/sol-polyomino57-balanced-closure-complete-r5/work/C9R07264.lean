import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R07264G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7264_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r7264targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r7264choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7264targets [(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)] c9r7264choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7264targets, c9r7264choice, ?_, checked⟩
    intro S h
    simp only [c9r7264targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 22 _ (by rfl)
  have c9r7265_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r7265targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r7265choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7265targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r7265choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7265targets, c9r7265choice, ?_, checked⟩
    intro S h
    simp only [c9r7265targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 29 _ (by rfl)
  have c9r7266_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r7266targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r7266choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7266targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r7266choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7266targets, c9r7266choice, ?_, checked⟩
    intro S h
    simp only [c9r7266targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 1 _ (by rfl)
  have c9r7267_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r7267targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r7267choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7267targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r7267choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7267targets, c9r7267choice, ?_, checked⟩
    intro S h
    simp only [c9r7267targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 4 _ (by rfl)
  have c9r7268_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r7268targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r7268choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7268targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r7268choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7268targets, c9r7268choice, ?_, checked⟩
    intro S h
    simp only [c9r7268targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 6 _ (by rfl)
  have c9r7269_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r7269targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r7269choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7269targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r7269choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7269targets, c9r7269choice, ?_, checked⟩
    intro S h
    simp only [c9r7269targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 8 _ (by rfl)
  have c9r7270_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r7270targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r7270choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7270targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] c9r7270choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7270targets, c9r7270choice, ?_, checked⟩
    intro S h
    simp only [c9r7270targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 11 _ (by rfl)
  have c9r7271_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c9r7271targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c9r7271choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7271targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] c9r7271choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7271targets, c9r7271choice, ?_, checked⟩
    intro S h
    simp only [c9r7271targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7264_closed
  · subst row; exact c9r7265_closed
  · subst row; exact c9r7266_closed
  · subst row; exact c9r7267_closed
  · subst row; exact c9r7268_closed
  · subst row; exact c9r7269_closed
  · subst row; exact c9r7270_closed
  · subst row; exact c9r7271_closed
theorem C9R07264G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7272_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c9r7272targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c9r7272choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7272targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] c9r7272choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7272targets, c9r7272choice, ?_, checked⟩
    intro S h
    simp only [c9r7272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 16 _ (by rfl)
  have c9r7273_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c9r7273targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c9r7273choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r7273targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] c9r7273choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7273targets, c9r7273choice, ?_, checked⟩
    intro S h
    simp only [c9r7273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 19 _ (by rfl)
  have c9r7274_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c9r7274targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c9r7274choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7274targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] c9r7274choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7274targets, c9r7274choice, ?_, checked⟩
    intro S h
    simp only [c9r7274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 22 _ (by rfl)
  have c9r7275_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c9r7275targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c9r7275choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7275targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] c9r7275choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7275targets, c9r7275choice, ?_, checked⟩
    intro S h
    simp only [c9r7275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 25 _ (by rfl)
  have c9r7276_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c9r7276targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c9r7276choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7276targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] c9r7276choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7276targets, c9r7276choice, ?_, checked⟩
    intro S h
    simp only [c9r7276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 28 _ (by rfl)
  have c9r7277_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c9r7277targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c9r7277choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7277targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)] c9r7277choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7277targets, c9r7277choice, ?_, checked⟩
    intro S h
    simp only [c9r7277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 1 _ (by rfl)
  have c9r7278_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c9r7278targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c9r7278choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7278targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)] c9r7278choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7278targets, c9r7278choice, ?_, checked⟩
    intro S h
    simp only [c9r7278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 3 _ (by rfl)
  have c9r7279_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c9r7279targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c9r7279choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7279targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)] c9r7279choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7279targets, c9r7279choice, ?_, checked⟩
    intro S h
    simp only [c9r7279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7272_closed
  · subst row; exact c9r7273_closed
  · subst row; exact c9r7274_closed
  · subst row; exact c9r7275_closed
  · subst row; exact c9r7276_closed
  · subst row; exact c9r7277_closed
  · subst row; exact c9r7278_closed
  · subst row; exact c9r7279_closed
theorem C9R07264G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7280_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c9r7280targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c9r7280choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7280targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)] c9r7280choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7280targets, c9r7280choice, ?_, checked⟩
    intro S h
    simp only [c9r7280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 8 _ (by rfl)
  have c9r7281_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c9r7281targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c9r7281choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7281targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)] c9r7281choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7281targets, c9r7281choice, ?_, checked⟩
    intro S h
    simp only [c9r7281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 10 _ (by rfl)
  have c9r7282_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c9r7282targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c9r7282choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7282targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)] c9r7282choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7282targets, c9r7282choice, ?_, checked⟩
    intro S h
    simp only [c9r7282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 14 _ (by rfl)
  have c9r7283_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c9r7283targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c9r7283choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7283targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)] c9r7283choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7283targets, c9r7283choice, ?_, checked⟩
    intro S h
    simp only [c9r7283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 17 _ (by rfl)
  have c9r7284_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c9r7284targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c9r7284choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7284targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)] c9r7284choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7284targets, c9r7284choice, ?_, checked⟩
    intro S h
    simp only [c9r7284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 19 _ (by rfl)
  have c9r7285_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c9r7285targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c9r7285choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7285targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)] c9r7285choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7285targets, c9r7285choice, ?_, checked⟩
    intro S h
    simp only [c9r7285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 22 _ (by rfl)
  have c9r7286_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c9r7286targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c9r7286choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7286targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)] c9r7286choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7286targets, c9r7286choice, ?_, checked⟩
    intro S h
    simp only [c9r7286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 25 _ (by rfl)
  have c9r7287_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c9r7287targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c9r7287choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7287targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)] c9r7287choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7287targets, c9r7287choice, ?_, checked⟩
    intro S h
    simp only [c9r7287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7280_closed
  · subst row; exact c9r7281_closed
  · subst row; exact c9r7282_closed
  · subst row; exact c9r7283_closed
  · subst row; exact c9r7284_closed
  · subst row; exact c9r7285_closed
  · subst row; exact c9r7286_closed
  · subst row; exact c9r7287_closed
theorem C9R07264G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7288_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r7288targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r7288choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7288targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)] c9r7288choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7288targets, c9r7288choice, ?_, checked⟩
    intro S h
    simp only [c9r7288targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 2 _ (by rfl)
  have c9r7289_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)] := by
    let c9r7289targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c9r7289choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7289targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)] c9r7289choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7289targets, c9r7289choice, ?_, checked⟩
    intro S h
    simp only [c9r7289targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 7 _ (by rfl)
  have c9r7290_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r7290targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r7290choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7290targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)] c9r7290choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7290targets, c9r7290choice, ?_, checked⟩
    intro S h
    simp only [c9r7290targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 11 _ (by rfl)
  have c9r7291_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r7291targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r7291choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7291targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)] c9r7291choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7291targets, c9r7291choice, ?_, checked⟩
    intro S h
    simp only [c9r7291targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 13 _ (by rfl)
  have c9r7292_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r7292targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r7292choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7292targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)] c9r7292choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7292targets, c9r7292choice, ?_, checked⟩
    intro S h
    simp only [c9r7292targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 15 _ (by rfl)
  have c9r7293_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r7293targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r7293choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7293targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)] c9r7293choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7293targets, c9r7293choice, ?_, checked⟩
    intro S h
    simp only [c9r7293targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 19 _ (by rfl)
  have c9r7294_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)] := by
    let c9r7294targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2),(4,2)]]
    let c9r7294choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7294targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)] c9r7294choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7294targets, c9r7294choice, ?_, checked⟩
    intro S h
    simp only [c9r7294targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 22 _ (by rfl)
  have c9r7295_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)] := by
    let c9r7295targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3),(4,3)]]
    let c9r7295choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7295targets [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,3)] c9r7295choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7295targets, c9r7295choice, ?_, checked⟩
    intro S h
    simp only [c9r7295targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 25 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7288_closed
  · subst row; exact c9r7289_closed
  · subst row; exact c9r7290_closed
  · subst row; exact c9r7291_closed
  · subst row; exact c9r7292_closed
  · subst row; exact c9r7293_closed
  · subst row; exact c9r7294_closed
  · subst row; exact c9r7295_closed
theorem C9R07264_closed (row : List GridPoint) (h : FamilyMember row F9B003L35) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L35, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R07264G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07264G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07264G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07264G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07264G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07264G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07264G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07264G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07264G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07264G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07264G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07264G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07264G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07264G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07264G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07264G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07264G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07264G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07264G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07264G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07264G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07264G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07264G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07264G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07264G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07264G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07264G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07264G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07264G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07264G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07264G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07264G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
