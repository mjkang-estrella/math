import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03360G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3360_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)] := by
    let c9r3360targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,2)]]
    let c9r3360choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3360targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)] c9r3360choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3360targets, c9r3360choice, ?_, checked⟩
    intro S h
    simp only [c9r3360targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 19 _ (by rfl)
  have c9r3361_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)] := by
    let c9r3361targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1),(8,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1),(8,1)]]
    let c9r3361choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3361targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)] c9r3361choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3361targets, c9r3361choice, ?_, checked⟩
    intro S h
    simp only [c9r3361targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 22 _ (by rfl)
  have c9r3362_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)] := by
    let c9r3362targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)]]
    let c9r3362choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3362targets [(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)] c9r3362choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3362targets, c9r3362choice, ?_, checked⟩
    intro S h
    simp only [c9r3362targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 29 _ (by rfl)
  have c9r3363_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r3363targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r3363choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3363targets [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] c9r3363choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3363targets, c9r3363choice, ?_, checked⟩
    intro S h
    simp only [c9r3363targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 2 _ (by rfl)
  have c9r3364_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)] := by
    let c9r3364targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5)],[(0,0),(0,1),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,4)]]
    let c9r3364choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3364targets [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)] c9r3364choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3364targets, c9r3364choice, ?_, checked⟩
    intro S h
    simp only [c9r3364targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 7 _ (by rfl)
  have c9r3365_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r3365targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,0)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r3365choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3365targets [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)] c9r3365choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3365targets, c9r3365choice, ?_, checked⟩
    intro S h
    simp only [c9r3365targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 10 _ (by rfl)
  have c9r3366_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r3366targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r3366choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3366targets [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)] c9r3366choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3366targets, c9r3366choice, ?_, checked⟩
    intro S h
    simp only [c9r3366targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 12 _ (by rfl)
  have c9r3367_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r3367targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r3367choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3367targets [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)] c9r3367choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3367targets, c9r3367choice, ?_, checked⟩
    intro S h
    simp only [c9r3367targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3360_closed
  · subst row; exact c9r3361_closed
  · subst row; exact c9r3362_closed
  · subst row; exact c9r3363_closed
  · subst row; exact c9r3364_closed
  · subst row; exact c9r3365_closed
  · subst row; exact c9r3366_closed
  · subst row; exact c9r3367_closed
theorem C9R03360G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3368_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r3368targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r3368choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3368targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r3368choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3368targets, c9r3368choice, ?_, checked⟩
    intro S h
    simp only [c9r3368targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 21 _ (by rfl)
  have c9r3369_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r3369targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r3369choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3369targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r3369choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3369targets, c9r3369choice, ?_, checked⟩
    intro S h
    simp only [c9r3369targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 25 _ (by rfl)
  have c9r3370_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r3370targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r3370choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3370targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r3370choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3370targets, c9r3370choice, ?_, checked⟩
    intro S h
    simp only [c9r3370targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 28 _ (by rfl)
  have c9r3371_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r3371targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r3371choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3371targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r3371choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3371targets, c9r3371choice, ?_, checked⟩
    intro S h
    simp only [c9r3371targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 30 _ (by rfl)
  have c9r3372_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r3372targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r3372choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3372targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r3372choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3372targets, c9r3372choice, ?_, checked⟩
    intro S h
    simp only [c9r3372targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 0 _ (by rfl)
  have c9r3373_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r3373targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r3373choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3373targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)] c9r3373choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3373targets, c9r3373choice, ?_, checked⟩
    intro S h
    simp only [c9r3373targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 3 _ (by rfl)
  have c9r3374_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c9r3374targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c9r3374choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3374targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)] c9r3374choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3374targets, c9r3374choice, ?_, checked⟩
    intro S h
    simp only [c9r3374targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 6 _ (by rfl)
  have c9r3375_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c9r3375targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c9r3375choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3375targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)] c9r3375choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3375targets, c9r3375choice, ?_, checked⟩
    intro S h
    simp only [c9r3375targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3368_closed
  · subst row; exact c9r3369_closed
  · subst row; exact c9r3370_closed
  · subst row; exact c9r3371_closed
  · subst row; exact c9r3372_closed
  · subst row; exact c9r3373_closed
  · subst row; exact c9r3374_closed
  · subst row; exact c9r3375_closed
theorem C9R03360G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3376_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c9r3376targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c9r3376choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3376targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)] c9r3376choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3376targets, c9r3376choice, ?_, checked⟩
    intro S h
    simp only [c9r3376targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 11 _ (by rfl)
  have c9r3377_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c9r3377targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c9r3377choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3377targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)] c9r3377choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3377targets, c9r3377choice, ?_, checked⟩
    intro S h
    simp only [c9r3377targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 14 _ (by rfl)
  have c9r3378_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c9r3378targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c9r3378choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3378targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)] c9r3378choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3378targets, c9r3378choice, ?_, checked⟩
    intro S h
    simp only [c9r3378targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 17 _ (by rfl)
  have c9r3379_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c9r3379targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c9r3379choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3379targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)] c9r3379choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3379targets, c9r3379choice, ?_, checked⟩
    intro S h
    simp only [c9r3379targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 20 _ (by rfl)
  have c9r3380_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r3380targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r3380choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3380targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)] c9r3380choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3380targets, c9r3380choice, ?_, checked⟩
    intro S h
    simp only [c9r3380targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 26 _ (by rfl)
  have c9r3381_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r3381targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r3381choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3381targets [(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r3381choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3381targets, c9r3381choice, ?_, checked⟩
    intro S h
    simp only [c9r3381targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 2 _ (by rfl)
  have c9r3382_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r3382targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r3382choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3382targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r3382choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3382targets, c9r3382choice, ?_, checked⟩
    intro S h
    simp only [c9r3382targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 10 _ (by rfl)
  have c9r3383_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] := by
    let c9r3383targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c9r3383choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3383targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] c9r3383choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3383targets, c9r3383choice, ?_, checked⟩
    intro S h
    simp only [c9r3383targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3376_closed
  · subst row; exact c9r3377_closed
  · subst row; exact c9r3378_closed
  · subst row; exact c9r3379_closed
  · subst row; exact c9r3380_closed
  · subst row; exact c9r3381_closed
  · subst row; exact c9r3382_closed
  · subst row; exact c9r3383_closed
theorem C9R03360G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3384_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r3384targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r3384choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3384targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r3384choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3384targets, c9r3384choice, ?_, checked⟩
    intro S h
    simp only [c9r3384targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 19 _ (by rfl)
  have c9r3385_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r3385targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r3385choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3385targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r3385choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3385targets, c9r3385choice, ?_, checked⟩
    intro S h
    simp only [c9r3385targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 22 _ (by rfl)
  have c9r3386_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r3386targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r3386choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3386targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r3386choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3386targets, c9r3386choice, ?_, checked⟩
    intro S h
    simp only [c9r3386targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 24 _ (by rfl)
  have c9r3387_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r3387targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r3387choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3387targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r3387choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3387targets, c9r3387choice, ?_, checked⟩
    intro S h
    simp only [c9r3387targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 26 _ (by rfl)
  have c9r3388_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r3388targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r3388choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3388targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r3388choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3388targets, c9r3388choice, ?_, checked⟩
    intro S h
    simp only [c9r3388targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 30 _ (by rfl)
  have c9r3389_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] := by
    let c9r3389targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)]]
    let c9r3389choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3389targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] c9r3389choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3389targets, c9r3389choice, ?_, checked⟩
    intro S h
    simp only [c9r3389targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 1 _ (by rfl)
  have c9r3390_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] := by
    let c9r3390targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)]]
    let c9r3390choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3390targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] c9r3390choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3390targets, c9r3390choice, ?_, checked⟩
    intro S h
    simp only [c9r3390targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 4 _ (by rfl)
  have c9r3391_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] := by
    let c9r3391targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)]]
    let c9r3391choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3391targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)] c9r3391choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3391targets, c9r3391choice, ?_, checked⟩
    intro S h
    simp only [c9r3391targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,false,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3384_closed
  · subst row; exact c9r3385_closed
  · subst row; exact c9r3386_closed
  · subst row; exact c9r3387_closed
  · subst row; exact c9r3388_closed
  · subst row; exact c9r3389_closed
  · subst row; exact c9r3390_closed
  · subst row; exact c9r3391_closed
theorem C9R03360_closed (row : List GridPoint) (h : FamilyMember row F9B001L41) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L41, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03360G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03360G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03360G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03360G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03360G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03360G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03360G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03360G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03360G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03360G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03360G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03360G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03360G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03360G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03360G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03360G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03360G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03360G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03360G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03360G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03360G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03360G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03360G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03360G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03360G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03360G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03360G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03360G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03360G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03360G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03360G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03360G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
