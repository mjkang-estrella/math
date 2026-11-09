import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R00544G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r544_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4)] := by
    let c10r544targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(3,4)]]
    let c10r544choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r544targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4)] c10r544choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r544targets, c10r544choice, ?_, checked⟩
    intro S h
    simp only [c10r544targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 26 _ (by rfl)
  have c10r545_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0)] := by
    let c10r545targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0),(4,0)]]
    let c10r545choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (14,(0,0)) else (15,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r545targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0)] c10r545choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r545targets, c10r545choice, ?_, checked⟩
    intro S h
    simp only [c10r545targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 29 _ (by rfl)
  have c10r546_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,3)] := by
    let c10r546targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,3),(4,3)]]
    let c10r546choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r546targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,3)] c10r546choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r546targets, c10r546choice, ?_, checked⟩
    intro S h
    simp only [c10r546targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 0 _ (by rfl)
  have c10r547_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1)] := by
    let c10r547targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1),(4,1)]]
    let c10r547choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (13,(0,0)) else (14,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r547targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1)] c10r547choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r547targets, c10r547choice, ?_, checked⟩
    intro S h
    simp only [c10r547targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 3 _ (by rfl)
  have c10r548_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(4,0)] := by
    let c10r548targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(5,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(4,0),(5,0)]]
    let c10r548choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,1)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (16,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r548targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(4,0)] c10r548choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r548targets, c10r548choice, ?_, checked⟩
    intro S h
    simp only [c10r548targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 5 _ (by rfl)
  have c10r549_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3)] := by
    let c10r549targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,1),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c10r549choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r549targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3)] c10r549choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r549targets, c10r549choice, ?_, checked⟩
    intro S h
    simp only [c10r549targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 9 _ (by rfl)
  have c10r550_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4)] := by
    let c10r550targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(3,4)]]
    let c10r550choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r550targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4)] c10r550choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r550targets, c10r550choice, ?_, checked⟩
    intro S h
    simp only [c10r550targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 13 _ (by rfl)
  have c10r551_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2)] := by
    let c10r551targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c10r551choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r551targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2)] c10r551choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r551targets, c10r551choice, ?_, checked⟩
    intro S h
    simp only [c10r551targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r544_closed
  · subst row; exact c10r545_closed
  · subst row; exact c10r546_closed
  · subst row; exact c10r547_closed
  · subst row; exact c10r548_closed
  · subst row; exact c10r549_closed
  · subst row; exact c10r550_closed
  · subst row; exact c10r551_closed
theorem C10R00544G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r552_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,3)] := by
    let c10r552targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c10r552choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r552targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,3)] c10r552choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r552targets, c10r552choice, ?_, checked⟩
    intro S h
    simp only [c10r552targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 18 _ (by rfl)
  have c10r553_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5)] := by
    let c10r553targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c10r553choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r553targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5)] c10r553choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r553targets, c10r553choice, ?_, checked⟩
    intro S h
    simp only [c10r553targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 22 _ (by rfl)
  have c10r554_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3)] := by
    let c10r554targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c10r554choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r554targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3)] c10r554choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r554targets, c10r554choice, ?_, checked⟩
    intro S h
    simp only [c10r554targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 25 _ (by rfl)
  have c10r555_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,4)] := by
    let c10r555targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c10r555choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r555targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,4)] c10r555choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r555targets, c10r555choice, ?_, checked⟩
    intro S h
    simp only [c10r555targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 27 _ (by rfl)
  have c10r556_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3)] := by
    let c10r556targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c10r556choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r556targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3)] c10r556choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r556targets, c10r556choice, ?_, checked⟩
    intro S h
    simp only [c10r556targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 31 _ (by rfl)
  have c10r557_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(3,4)] := by
    let c10r557targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c10r557choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r557targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(3,4)] c10r557choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r557targets, c10r557choice, ?_, checked⟩
    intro S h
    simp only [c10r557targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 2 _ (by rfl)
  have c10r558_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(4,3)] := by
    let c10r558targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,3),(4,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(4,3),(5,3)]]
    let c10r558choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r558targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3),(3,3),(4,3)] c10r558choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r558targets, c10r558choice, ?_, checked⟩
    intro S h
    simp only [c10r558targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 5 _ (by rfl)
  have c10r559_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7)] := by
    let c10r559targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,7),(1,0),(1,4),(1,5),(1,6),(1,7)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,7)]]
    let c10r559choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (11,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (16,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r559targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7)] c10r559choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r559targets, c10r559choice, ?_, checked⟩
    intro S h
    simp only [c10r559targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r552_closed
  · subst row; exact c10r553_closed
  · subst row; exact c10r554_closed
  · subst row; exact c10r555_closed
  · subst row; exact c10r556_closed
  · subst row; exact c10r557_closed
  · subst row; exact c10r558_closed
  · subst row; exact c10r559_closed
theorem C10R00544G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r560_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0)] := by
    let c10r560targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(3,0)]]
    let c10r560choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r560targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0)] c10r560choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r560targets, c10r560choice, ?_, checked⟩
    intro S h
    simp only [c10r560targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 16 _ (by rfl)
  have c10r561_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4)] := by
    let c10r561targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4),(3,4)]]
    let c10r561choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r561targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4)] c10r561choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r561targets, c10r561choice, ?_, checked⟩
    intro S h
    simp only [c10r561targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 20 _ (by rfl)
  have c10r562_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,5)] := by
    let c10r562targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,5),(3,5)]]
    let c10r562choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r562targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,5)] c10r562choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r562targets, c10r562choice, ?_, checked⟩
    intro S h
    simp only [c10r562targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 22 _ (by rfl)
  have c10r563_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,6)] := by
    let c10r563targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,0),(1,4),(1,5),(1,6),(2,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,6),(3,6)]]
    let c10r563choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r563targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,6)] c10r563choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r563targets, c10r563choice, ?_, checked⟩
    intro S h
    simp only [c10r563targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 24 _ (by rfl)
  have c10r564_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1)] := by
    let c10r564targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(3,1)]]
    let c10r564choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r564targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1)] c10r564choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r564targets, c10r564choice, ?_, checked⟩
    intro S h
    simp only [c10r564targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 29 _ (by rfl)
  have c10r565_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4)] := by
    let c10r565targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(3,4)]]
    let c10r565choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r565targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4)] c10r565choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r565targets, c10r565choice, ?_, checked⟩
    intro S h
    simp only [c10r565targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 1 _ (by rfl)
  have c10r566_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5)] := by
    let c10r566targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,1),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,1),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,0),(2,1),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5),(3,5)]]
    let c10r566choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r566targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5)] c10r566choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r566targets, c10r566choice, ?_, checked⟩
    intro S h
    simp only [c10r566targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 4 _ (by rfl)
  have c10r567_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(3,0)] := by
    let c10r567targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(3,0),(4,0)]]
    let c10r567choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r567targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(3,0)] c10r567choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r567targets, c10r567choice, ?_, checked⟩
    intro S h
    simp only [c10r567targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r560_closed
  · subst row; exact c10r561_closed
  · subst row; exact c10r562_closed
  · subst row; exact c10r563_closed
  · subst row; exact c10r564_closed
  · subst row; exact c10r565_closed
  · subst row; exact c10r566_closed
  · subst row; exact c10r567_closed
theorem C10R00544G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r568_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4)] := by
    let c10r568targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4),(3,4)]]
    let c10r568choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r568targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4)] c10r568choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r568targets, c10r568choice, ?_, checked⟩
    intro S h
    simp only [c10r568targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 10 _ (by rfl)
  have c10r569_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5)] := by
    let c10r569targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(3,5)]]
    let c10r569choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r569targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5)] c10r569choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r569targets, c10r569choice, ?_, checked⟩
    intro S h
    simp only [c10r569targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 13 _ (by rfl)
  have c10r570_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,4)] := by
    let c10r570targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,4),(4,4)]]
    let c10r570choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r570targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,4)] c10r570choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r570targets, c10r570choice, ?_, checked⟩
    intro S h
    simp only [c10r570targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 16 _ (by rfl)
  have c10r571_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(2,6)] := by
    let c10r571targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(3,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5),(2,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(2,6),(3,6)]]
    let c10r571choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r571targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(2,6)] c10r571choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r571targets, c10r571choice, ?_, checked⟩
    intro S h
    simp only [c10r571targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 19 _ (by rfl)
  have c10r572_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(3,5)] := by
    let c10r572targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(4,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5),(3,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(3,5),(4,5)]]
    let c10r572choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r572targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,5),(3,5)] c10r572choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r572targets, c10r572choice, ?_, checked⟩
    intro S h
    simp only [c10r572targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 22 _ (by rfl)
  have c10r573_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2)] := by
    let c10r573targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c10r573choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r573targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2)] c10r573choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r573targets, c10r573choice, ?_, checked⟩
    intro S h
    simp only [c10r573targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 28 _ (by rfl)
  have c10r574_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4)] := by
    let c10r574targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(3,4)]]
    let c10r574choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r574targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4)] c10r574choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r574targets, c10r574choice, ?_, checked⟩
    intro S h
    simp only [c10r574targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 1 _ (by rfl)
  have c10r575_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0)] := by
    let c10r575targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c10r575choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r575targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0)] c10r575choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r575targets, c10r575choice, ?_, checked⟩
    intro S h
    simp only [c10r575targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r568_closed
  · subst row; exact c10r569_closed
  · subst row; exact c10r570_closed
  · subst row; exact c10r571_closed
  · subst row; exact c10r572_closed
  · subst row; exact c10r573_closed
  · subst row; exact c10r574_closed
  · subst row; exact c10r575_closed
theorem C10R00544_closed (row : List GridPoint) (h : FamilyMember row F10B000L17) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L17, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R00544G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00544G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00544G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00544G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00544G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00544G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00544G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00544G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00544G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00544G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00544G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00544G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00544G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00544G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00544G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00544G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00544G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00544G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00544G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00544G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00544G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00544G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00544G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00544G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00544G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00544G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00544G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00544G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00544G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00544G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00544G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00544G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
