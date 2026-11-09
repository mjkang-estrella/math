import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R00576G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r576_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,1)] := by
    let c10r576targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c10r576choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r576targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,1)] c10r576choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r576targets, c10r576choice, ?_, checked⟩
    intro S h
    simp only [c10r576targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 5 _ (by rfl)
  have c10r577_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4)] := by
    let c10r577targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(3,4)]]
    let c10r577choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r577targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4)] c10r577choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r577targets, c10r577choice, ?_, checked⟩
    intro S h
    simp only [c10r577targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 10 _ (by rfl)
  have c10r578_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5)] := by
    let c10r578targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(3,5)]]
    let c10r578choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r578targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5)] c10r578choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r578targets, c10r578choice, ?_, checked⟩
    intro S h
    simp only [c10r578targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 14 _ (by rfl)
  have c10r579_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0)] := by
    let c10r579targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,5),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(2,5),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(2,5),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,5),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0),(4,0)]]
    let c10r579choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (15,(0,0)) else (16,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (17,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r579targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0)] c10r579choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r579targets, c10r579choice, ?_, checked⟩
    intro S h
    simp only [c10r579targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 17 _ (by rfl)
  have c10r580_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,4)] := by
    let c10r580targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,4),(4,4)]]
    let c10r580choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (17,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r580targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,4)] c10r580choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r580targets, c10r580choice, ?_, checked⟩
    intro S h
    simp only [c10r580targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 20 _ (by rfl)
  have c10r581_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1)] := by
    let c10r581targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1),(4,1)]]
    let c10r581choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (14,(0,0)) else (15,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r581targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1)] c10r581choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r581targets, c10r581choice, ?_, checked⟩
    intro S h
    simp only [c10r581targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 23 _ (by rfl)
  have c10r582_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(4,0)] := by
    let c10r582targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(5,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(4,0),(5,0)]]
    let c10r582choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (15,(0,1)) else (16,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (17,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r582targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(4,0)] c10r582choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r582targets, c10r582choice, ?_, checked⟩
    intro S h
    simp only [c10r582targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 25 _ (by rfl)
  have c10r583_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4)] := by
    let c10r583targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,2),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c10r583choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r583targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4)] c10r583choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r583targets, c10r583choice, ?_, checked⟩
    intro S h
    simp only [c10r583targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r576_closed
  · subst row; exact c10r577_closed
  · subst row; exact c10r578_closed
  · subst row; exact c10r579_closed
  · subst row; exact c10r580_closed
  · subst row; exact c10r581_closed
  · subst row; exact c10r582_closed
  · subst row; exact c10r583_closed
theorem C10R00576G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r584_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5)] := by
    let c10r584targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(3,5)]]
    let c10r584choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r584targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5)] c10r584choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r584targets, c10r584choice, ?_, checked⟩
    intro S h
    simp only [c10r584targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 2 _ (by rfl)
  have c10r585_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,3)] := by
    let c10r585targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,3),(4,3)]]
    let c10r585choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r585targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,3)] c10r585choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r585targets, c10r585choice, ?_, checked⟩
    intro S h
    simp only [c10r585targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,false,true,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 5 _ (by rfl)
  have c10r586_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,4)] := by
    let c10r586targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,4),(4,4)]]
    let c10r586choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r586targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,4)] c10r586choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r586targets, c10r586choice, ?_, checked⟩
    intro S h
    simp only [c10r586targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 7 _ (by rfl)
  have c10r587_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6)] := by
    let c10r587targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(3,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5),(2,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,6),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6),(3,6)]]
    let c10r587choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r587targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6)] c10r587choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r587targets, c10r587choice, ?_, checked⟩
    intro S h
    simp only [c10r587targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 11 _ (by rfl)
  have c10r588_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,4)] := by
    let c10r588targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,4),(4,4)]]
    let c10r588choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r588targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,4)] c10r588choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r588targets, c10r588choice, ?_, checked⟩
    intro S h
    simp only [c10r588targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 14 _ (by rfl)
  have c10r589_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,5)] := by
    let c10r589targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5),(3,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,5),(4,5)]]
    let c10r589choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r589targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,5)] c10r589choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r589targets, c10r589choice, ?_, checked⟩
    intro S h
    simp only [c10r589targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 16 _ (by rfl)
  have c10r590_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,3),(3,4)] := by
    let c10r590targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,3),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,3),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,3),(3,4),(4,4)]]
    let c10r590choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r590targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,3),(3,4)] c10r590choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r590targets, c10r590choice, ?_, checked⟩
    intro S h
    simp only [c10r590targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 20 _ (by rfl)
  have c10r591_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(3,5)] := by
    let c10r591targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(4,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,4),(3,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(3,5),(4,5)]]
    let c10r591choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r591targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(3,5)] c10r591choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r591targets, c10r591choice, ?_, checked⟩
    intro S h
    simp only [c10r591targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r584_closed
  · subst row; exact c10r585_closed
  · subst row; exact c10r586_closed
  · subst row; exact c10r587_closed
  · subst row; exact c10r588_closed
  · subst row; exact c10r589_closed
  · subst row; exact c10r590_closed
  · subst row; exact c10r591_closed
theorem C10R00576G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r592_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(4,4)] := by
    let c10r592targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(5,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,4),(4,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(4,4),(5,4)]]
    let c10r592choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (17,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r592targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4),(3,4),(4,4)] c10r592choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r592targets, c10r592choice, ?_, checked⟩
    intro S h
    simp only [c10r592targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 26 _ (by rfl)
  have c10r593_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3)] := by
    let c10r593targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c10r593choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r593targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3)] c10r593choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r593targets, c10r593choice, ?_, checked⟩
    intro S h
    simp only [c10r593targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 31 _ (by rfl)
  have c10r594_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0)] := by
    let c10r594targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c10r594choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (13,(0,0)) else (14,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r594targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0)] c10r594choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r594targets, c10r594choice, ?_, checked⟩
    intro S h
    simp only [c10r594targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 2 _ (by rfl)
  have c10r595_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1)] := by
    let c10r595targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c10r595choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r595targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1)] c10r595choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r595targets, c10r595choice, ?_, checked⟩
    intro S h
    simp only [c10r595targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 4 _ (by rfl)
  have c10r596_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,2)] := by
    let c10r596targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c10r596choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r596targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,2)] c10r596choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r596targets, c10r596choice, ?_, checked⟩
    intro S h
    simp only [c10r596targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 6 _ (by rfl)
  have c10r597_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1)] := by
    let c10r597targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)]]
    let c10r597choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (13,(0,0)) else (14,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r597targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1)] c10r597choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r597targets, c10r597choice, ?_, checked⟩
    intro S h
    simp only [c10r597targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 9 _ (by rfl)
  have c10r598_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(4,0)] := by
    let c10r598targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)]]
    let c10r598choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,1)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (16,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r598targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(4,0)] c10r598choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r598targets, c10r598choice, ?_, checked⟩
    intro S h
    simp only [c10r598targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 11 _ (by rfl)
  have c10r599_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(3,2)] := by
    let c10r599targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)]]
    let c10r599choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r599targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(3,2)] c10r599choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r599targets, c10r599choice, ?_, checked⟩
    intro S h
    simp only [c10r599targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r592_closed
  · subst row; exact c10r593_closed
  · subst row; exact c10r594_closed
  · subst row; exact c10r595_closed
  · subst row; exact c10r596_closed
  · subst row; exact c10r597_closed
  · subst row; exact c10r598_closed
  · subst row; exact c10r599_closed
theorem C10R00576G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r600_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(4,1)] := by
    let c10r600targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)]]
    let c10r600choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (16,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r600targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,1),(4,1)] c10r600choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r600targets, c10r600choice, ?_, checked⟩
    intro S h
    simp only [c10r600targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 17 _ (by rfl)
  have c10r601_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2)] := by
    let c10r601targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)]]
    let c10r601choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,1)) else (16,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (17,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r601targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2)] c10r601choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r601targets, c10r601choice, ?_, checked⟩
    intro S h
    simp only [c10r601targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 22 _ (by rfl)
  have c10r602_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0)] := by
    let c10r602targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)]]
    let c10r602choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,1)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (16,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r602targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0)] c10r602choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r602targets, c10r602choice, ?_, checked⟩
    intro S h
    simp only [c10r602targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 24 _ (by rfl)
  have c10r603_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,1)] := by
    let c10r603targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)]]
    let c10r603choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (4,(1,0)) else (5,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,1)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (16,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r603targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,1)] c10r603choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r603targets, c10r603choice, ?_, checked⟩
    intro S h
    simp only [c10r603targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 26 _ (by rfl)
  have c10r604_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(4,1)] := by
    let c10r604targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)]]
    let c10r604choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (13,(0,0)) else (14,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (15,(0,0)) else (16,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (17,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (18,(0,0)) else (19,(0,0)))))))
    have checked : successorFastRowCheck c10r604targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(4,1)] c10r604choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r604targets, c10r604choice, ?_, checked⟩
    intro S h
    simp only [c10r604targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 29 _ (by rfl)
  have c10r605_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(5,0)] := by
    let c10r605targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)]]
    let c10r605choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (13,(0,0)) else (14,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (16,(0,1)) else (17,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (18,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (19,(0,0)) else (20,(0,0)))))))
    have checked : successorFastRowCheck c10r605targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0),(4,0),(5,0)] c10r605choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r605targets, c10r605choice, ?_, checked⟩
    intro S h
    simp only [c10r605targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,false,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,false] 31 _ (by rfl)
  have c10r606_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c10r606targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c10r606choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r606targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)] c10r606choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r606targets, c10r606choice, ?_, checked⟩
    intro S h
    simp only [c10r606targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 5 _ (by rfl)
  have c10r607_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c10r607targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c10r607choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (3,(1,0)) else (4,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r607targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)] c10r607choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r607targets, c10r607choice, ?_, checked⟩
    intro S h
    simp only [c10r607targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,false,true,true,true,true,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,false,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,true,false,true,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,false,false,false,true,true] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r600_closed
  · subst row; exact c10r601_closed
  · subst row; exact c10r602_closed
  · subst row; exact c10r603_closed
  · subst row; exact c10r604_closed
  · subst row; exact c10r605_closed
  · subst row; exact c10r606_closed
  · subst row; exact c10r607_closed
theorem C10R00576_closed (row : List GridPoint) (h : FamilyMember row F10B000L18) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L18, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R00576G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00576G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00576G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00576G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00576G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00576G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00576G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00576G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00576G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00576G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00576G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00576G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00576G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00576G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00576G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00576G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00576G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00576G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00576G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00576G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00576G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00576G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00576G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00576G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00576G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00576G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00576G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00576G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00576G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00576G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00576G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00576G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
