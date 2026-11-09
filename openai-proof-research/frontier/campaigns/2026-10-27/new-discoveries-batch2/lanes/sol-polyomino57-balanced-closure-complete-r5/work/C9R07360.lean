import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R07360G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7360_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r7360targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r7360choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7360targets [(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)] c9r7360choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7360targets, c9r7360choice, ?_, checked⟩
    intro S h
    simp only [c9r7360targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 3 _ (by rfl)
  have c9r7361_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r7361targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r7361choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7361targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)] c9r7361choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7361targets, c9r7361choice, ?_, checked⟩
    intro S h
    simp only [c9r7361targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 9 _ (by rfl)
  have c9r7362_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r7362targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r7362choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7362targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)] c9r7362choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7362targets, c9r7362choice, ?_, checked⟩
    intro S h
    simp only [c9r7362targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 12 _ (by rfl)
  have c9r7363_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r7363targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r7363choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r7363targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)] c9r7363choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7363targets, c9r7363choice, ?_, checked⟩
    intro S h
    simp only [c9r7363targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 14 _ (by rfl)
  have c9r7364_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r7364targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r7364choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7364targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)] c9r7364choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7364targets, c9r7364choice, ?_, checked⟩
    intro S h
    simp only [c9r7364targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 16 _ (by rfl)
  have c9r7365_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r7365targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r7365choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7365targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)] c9r7365choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7365targets, c9r7365choice, ?_, checked⟩
    intro S h
    simp only [c9r7365targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 19 _ (by rfl)
  have c9r7366_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r7366targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r7366choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7366targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)] c9r7366choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7366targets, c9r7366choice, ?_, checked⟩
    intro S h
    simp only [c9r7366targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 21 _ (by rfl)
  have c9r7367_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r7367targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r7367choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7367targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)] c9r7367choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7367targets, c9r7367choice, ?_, checked⟩
    intro S h
    simp only [c9r7367targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7360_closed
  · subst row; exact c9r7361_closed
  · subst row; exact c9r7362_closed
  · subst row; exact c9r7363_closed
  · subst row; exact c9r7364_closed
  · subst row; exact c9r7365_closed
  · subst row; exact c9r7366_closed
  · subst row; exact c9r7367_closed
theorem C9R07360G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7368_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r7368targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r7368choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7368targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)] c9r7368choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7368targets, c9r7368choice, ?_, checked⟩
    intro S h
    simp only [c9r7368targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 27 _ (by rfl)
  have c9r7369_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r7369targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r7369choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7369targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)] c9r7369choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7369targets, c9r7369choice, ?_, checked⟩
    intro S h
    simp only [c9r7369targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 0 _ (by rfl)
  have c9r7370_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r7370targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r7370choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7370targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)] c9r7370choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7370targets, c9r7370choice, ?_, checked⟩
    intro S h
    simp only [c9r7370targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 4 _ (by rfl)
  have c9r7371_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r7371targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r7371choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7371targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)] c9r7371choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7371targets, c9r7371choice, ?_, checked⟩
    intro S h
    simp only [c9r7371targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 6 _ (by rfl)
  have c9r7372_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r7372targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r7372choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7372targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)] c9r7372choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7372targets, c9r7372choice, ?_, checked⟩
    intro S h
    simp only [c9r7372targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 8 _ (by rfl)
  have c9r7373_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r7373targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r7373choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7373targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)] c9r7373choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7373targets, c9r7373choice, ?_, checked⟩
    intro S h
    simp only [c9r7373targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 11 _ (by rfl)
  have c9r7374_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r7374targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r7374choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7374targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)] c9r7374choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7374targets, c9r7374choice, ?_, checked⟩
    intro S h
    simp only [c9r7374targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 14 _ (by rfl)
  have c9r7375_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r7375targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r7375choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7375targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)] c9r7375choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7375targets, c9r7375choice, ?_, checked⟩
    intro S h
    simp only [c9r7375targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7368_closed
  · subst row; exact c9r7369_closed
  · subst row; exact c9r7370_closed
  · subst row; exact c9r7371_closed
  · subst row; exact c9r7372_closed
  · subst row; exact c9r7373_closed
  · subst row; exact c9r7374_closed
  · subst row; exact c9r7375_closed
theorem C9R07360G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7376_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r7376targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r7376choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r7376targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)] c9r7376choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7376targets, c9r7376choice, ?_, checked⟩
    intro S h
    simp only [c9r7376targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 20 _ (by rfl)
  have c9r7377_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r7377targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r7377choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7377targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)] c9r7377choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7377targets, c9r7377choice, ?_, checked⟩
    intro S h
    simp only [c9r7377targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 23 _ (by rfl)
  have c9r7378_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r7378targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r7378choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7378targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)] c9r7378choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7378targets, c9r7378choice, ?_, checked⟩
    intro S h
    simp only [c9r7378targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 28 _ (by rfl)
  have c9r7379_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r7379targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r7379choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7379targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r7379choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7379targets, c9r7379choice, ?_, checked⟩
    intro S h
    simp only [c9r7379targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 30 _ (by rfl)
  have c9r7380_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r7380targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r7380choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7380targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r7380choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7380targets, c9r7380choice, ?_, checked⟩
    intro S h
    simp only [c9r7380targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 0 _ (by rfl)
  have c9r7381_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r7381targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r7381choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7381targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)] c9r7381choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7381targets, c9r7381choice, ?_, checked⟩
    intro S h
    simp only [c9r7381targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 4 _ (by rfl)
  have c9r7382_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r7382targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r7382choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7382targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)] c9r7382choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7382targets, c9r7382choice, ?_, checked⟩
    intro S h
    simp only [c9r7382targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 7 _ (by rfl)
  have c9r7383_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r7383targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r7383choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7383targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)] c9r7383choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7383targets, c9r7383choice, ?_, checked⟩
    intro S h
    simp only [c9r7383targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7376_closed
  · subst row; exact c9r7377_closed
  · subst row; exact c9r7378_closed
  · subst row; exact c9r7379_closed
  · subst row; exact c9r7380_closed
  · subst row; exact c9r7381_closed
  · subst row; exact c9r7382_closed
  · subst row; exact c9r7383_closed
theorem C9R07360G3 (row : List GridPoint) (h : row ∈ [[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r7384_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r7384targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r7384choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7384targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)] c9r7384choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7384targets, c9r7384choice, ?_, checked⟩
    intro S h
    simp only [c9r7384targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 12 _ (by rfl)
  have c9r7385_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r7385targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r7385choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7385targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)] c9r7385choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7385targets, c9r7385choice, ?_, checked⟩
    intro S h
    simp only [c9r7385targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 15 _ (by rfl)
  have c9r7386_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r7386targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r7386choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r7386targets [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)] c9r7386choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7386targets, c9r7386choice, ?_, checked⟩
    intro S h
    simp only [c9r7386targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 18 _ (by rfl)
  have c9r7387_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r7387targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,6),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r7387choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r7387targets [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)] c9r7387choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7387targets, c9r7387choice, ?_, checked⟩
    intro S h
    simp only [c9r7387targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 24 _ (by rfl)
  have c9r7388_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)] := by
    let c9r7388targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)]]
    let c9r7388choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7388targets [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)] c9r7388choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7388targets, c9r7388choice, ?_, checked⟩
    intro S h
    simp only [c9r7388targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 29 _ (by rfl)
  have c9r7389_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)] := by
    let c9r7389targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c9r7389choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7389targets [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)] c9r7389choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7389targets, c9r7389choice, ?_, checked⟩
    intro S h
    simp only [c9r7389targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,false] 0 _ (by rfl)
  have c9r7390_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)] := by
    let c9r7390targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c9r7390choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r7390targets [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)] c9r7390choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7390targets, c9r7390choice, ?_, checked⟩
    intro S h
    simp only [c9r7390targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,false] 2 _ (by rfl)
  have c9r7391_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r7391targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r7391choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r7391targets [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)] c9r7391choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r7391targets, c9r7391choice, ?_, checked⟩
    intro S h
    simp only [c9r7391targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,false] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r7384_closed
  · subst row; exact c9r7385_closed
  · subst row; exact c9r7386_closed
  · subst row; exact c9r7387_closed
  · subst row; exact c9r7388_closed
  · subst row; exact c9r7389_closed
  · subst row; exact c9r7390_closed
  · subst row; exact c9r7391_closed
theorem C9R07360_closed (row : List GridPoint) (h : FamilyMember row F9B003L38) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L38, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R07360G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07360G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07360G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07360G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07360G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07360G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07360G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07360G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07360G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07360G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07360G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07360G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07360G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07360G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07360G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07360G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07360G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07360G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07360G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07360G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07360G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07360G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07360G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07360G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R07360G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R07360G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R07360G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R07360G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R07360G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R07360G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R07360G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R07360G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
