import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R01952G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1952_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)] := by
    let c10r1952targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3),(5,3)]]
    let c10r1952choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1952targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)] c10r1952choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1952targets, c10r1952choice, ?_, checked⟩
    intro S h
    simp only [c10r1952targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 24 _ (by rfl)
  have c10r1953_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)] := by
    let c10r1953targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5),(4,5)]]
    let c10r1953choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1953targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)] c10r1953choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1953targets, c10r1953choice, ?_, checked⟩
    intro S h
    simp only [c10r1953targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 27 _ (by rfl)
  have c10r1954_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)] := by
    let c10r1954targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4),(5,4)]]
    let c10r1954choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1954targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)] c10r1954choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1954targets, c10r1954choice, ?_, checked⟩
    intro S h
    simp only [c10r1954targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 30 _ (by rfl)
  have c10r1955_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)] := by
    let c10r1955targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,1),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c10r1955choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1955targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)] c10r1955choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1955targets, c10r1955choice, ?_, checked⟩
    intro S h
    simp only [c10r1955targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 4 _ (by rfl)
  have c10r1956_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)] := by
    let c10r1956targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(4,4)]]
    let c10r1956choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1956targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)] c10r1956choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1956targets, c10r1956choice, ?_, checked⟩
    intro S h
    simp only [c10r1956targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 8 _ (by rfl)
  have c10r1957_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)] := by
    let c10r1957targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2),(5,2)]]
    let c10r1957choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1957targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)] c10r1957choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1957targets, c10r1957choice, ?_, checked⟩
    intro S h
    simp only [c10r1957targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 11 _ (by rfl)
  have c10r1958_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)] := by
    let c10r1958targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3),(5,3)]]
    let c10r1958choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1958targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)] c10r1958choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1958targets, c10r1958choice, ?_, checked⟩
    intro S h
    simp only [c10r1958targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 13 _ (by rfl)
  have c10r1959_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)] := by
    let c10r1959targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(4,5)]]
    let c10r1959choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1959targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)] c10r1959choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1959targets, c10r1959choice, ?_, checked⟩
    intro S h
    simp only [c10r1959targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1952_closed
  · subst row; exact c10r1953_closed
  · subst row; exact c10r1954_closed
  · subst row; exact c10r1955_closed
  · subst row; exact c10r1956_closed
  · subst row; exact c10r1957_closed
  · subst row; exact c10r1958_closed
  · subst row; exact c10r1959_closed
theorem C10R01952G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1960_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)] := by
    let c10r1960targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3),(5,3)]]
    let c10r1960choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1960targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)] c10r1960choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1960targets, c10r1960choice, ?_, checked⟩
    intro S h
    simp only [c10r1960targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 20 _ (by rfl)
  have c10r1961_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)] := by
    let c10r1961targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4),(5,4)]]
    let c10r1961choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1961targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)] c10r1961choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1961targets, c10r1961choice, ?_, checked⟩
    intro S h
    simp only [c10r1961targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 22 _ (by rfl)
  have c10r1962_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)] := by
    let c10r1962targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,2),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,2),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(5,3)]]
    let c10r1962choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1962targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)] c10r1962choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1962targets, c10r1962choice, ?_, checked⟩
    intro S h
    simp only [c10r1962targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 26 _ (by rfl)
  have c10r1963_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)] := by
    let c10r1963targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4),(5,4)]]
    let c10r1963choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1963targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)] c10r1963choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1963targets, c10r1963choice, ?_, checked⟩
    intro S h
    simp only [c10r1963targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 29 _ (by rfl)
  have c10r1964_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)] := by
    let c10r1964targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(6,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(6,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(6,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3),(6,3)]]
    let c10r1964choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r1964targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)] c10r1964choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1964targets, c10r1964choice, ?_, checked⟩
    intro S h
    simp only [c10r1964targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 0 _ (by rfl)
  have c10r1965_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)] := by
    let c10r1965targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(3,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(3,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(3,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(2,7),(2,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,7),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7),(2,8)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7),(3,7)]]
    let c10r1965choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 8) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 7) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1965targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)] c10r1965choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1965targets, c10r1965choice, ?_, checked⟩
    intro S h
    simp only [c10r1965targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 5 _ (by rfl)
  have c10r1966_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)] := by
    let c10r1966targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(2,7),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4),(4,4)]]
    let c10r1966choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1966targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)] c10r1966choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1966targets, c10r1966choice, ?_, checked⟩
    intro S h
    simp only [c10r1966targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 9 _ (by rfl)
  have c10r1967_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)] := by
    let c10r1967targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(2,7),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5),(4,5)]]
    let c10r1967choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1967targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)] c10r1967choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1967targets, c10r1967choice, ?_, checked⟩
    intro S h
    simp only [c10r1967targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1960_closed
  · subst row; exact c10r1961_closed
  · subst row; exact c10r1962_closed
  · subst row; exact c10r1963_closed
  · subst row; exact c10r1964_closed
  · subst row; exact c10r1965_closed
  · subst row; exact c10r1966_closed
  · subst row; exact c10r1967_closed
theorem C10R01952G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1968_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)] := by
    let c10r1968targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(2,7),(3,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6),(4,6)]]
    let c10r1968choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 7) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1968targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)] c10r1968choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1968targets, c10r1968choice, ?_, checked⟩
    intro S h
    simp only [c10r1968targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 13 _ (by rfl)
  have c10r1969_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)] := by
    let c10r1969targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4),(4,4)]]
    let c10r1969choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1969targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)] c10r1969choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1969targets, c10r1969choice, ?_, checked⟩
    intro S h
    simp only [c10r1969targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 17 _ (by rfl)
  have c10r1970_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)] := by
    let c10r1970targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(4,5)]]
    let c10r1970choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1970targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)] c10r1970choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1970targets, c10r1970choice, ?_, checked⟩
    intro S h
    simp only [c10r1970targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 20 _ (by rfl)
  have c10r1971_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)] := by
    let c10r1971targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4),(5,4)]]
    let c10r1971choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1971targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)] c10r1971choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1971targets, c10r1971choice, ?_, checked⟩
    intro S h
    simp only [c10r1971targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 23 _ (by rfl)
  have c10r1972_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)] := by
    let c10r1972targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5),(4,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5),(4,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5),(4,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6),(4,6)]]
    let c10r1972choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 7) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1972targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)] c10r1972choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1972targets, c10r1972choice, ?_, checked⟩
    intro S h
    simp only [c10r1972targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 26 _ (by rfl)
  have c10r1973_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)] := by
    let c10r1973targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5),(5,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5),(5,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5),(5,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(3,6),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5),(5,5)]]
    let c10r1973choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1973targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)] c10r1973choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1973targets, c10r1973choice, ?_, checked⟩
    intro S h
    simp only [c10r1973targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 29 _ (by rfl)
  have c10r1974_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)] := by
    let c10r1974targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,2),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,2),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4),(4,4)]]
    let c10r1974choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1974targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)] c10r1974choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1974targets, c10r1974choice, ?_, checked⟩
    intro S h
    simp only [c10r1974targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 3 _ (by rfl)
  have c10r1975_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)] := by
    let c10r1975targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(4,5)]]
    let c10r1975choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1975targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)] c10r1975choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1975targets, c10r1975choice, ?_, checked⟩
    intro S h
    simp only [c10r1975targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1968_closed
  · subst row; exact c10r1969_closed
  · subst row; exact c10r1970_closed
  · subst row; exact c10r1971_closed
  · subst row; exact c10r1972_closed
  · subst row; exact c10r1973_closed
  · subst row; exact c10r1974_closed
  · subst row; exact c10r1975_closed
theorem C10R01952G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1976_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)] := by
    let c10r1976targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3),(5,3)]]
    let c10r1976choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1976targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)] c10r1976choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1976targets, c10r1976choice, ?_, checked⟩
    intro S h
    simp only [c10r1976targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 10 _ (by rfl)
  have c10r1977_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)] := by
    let c10r1977targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4),(5,4)]]
    let c10r1977choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1977targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)] c10r1977choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1977targets, c10r1977choice, ?_, checked⟩
    intro S h
    simp only [c10r1977targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 12 _ (by rfl)
  have c10r1978_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)] := by
    let c10r1978targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(4,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(4,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(4,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,5),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,6),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6),(4,6)]]
    let c10r1978choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 7) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1978targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)] c10r1978choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1978targets, c10r1978choice, ?_, checked⟩
    intro S h
    simp only [c10r1978targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 16 _ (by rfl)
  have c10r1979_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)] := by
    let c10r1979targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4),(5,4)]]
    let c10r1979choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1979targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)] c10r1979choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1979targets, c10r1979choice, ?_, checked⟩
    intro S h
    simp only [c10r1979targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 19 _ (by rfl)
  have c10r1980_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)] := by
    let c10r1980targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(5,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(5,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(5,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,5),(3,6),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5),(5,5)]]
    let c10r1980choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1980targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)] c10r1980choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1980targets, c10r1980choice, ?_, checked⟩
    intro S h
    simp only [c10r1980targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 21 _ (by rfl)
  have c10r1981_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)] := by
    let c10r1981targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,3),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,3),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,3),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4),(5,4)]]
    let c10r1981choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1981targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)] c10r1981choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1981targets, c10r1981choice, ?_, checked⟩
    intro S h
    simp only [c10r1981targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 25 _ (by rfl)
  have c10r1982_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)] := by
    let c10r1982targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4),(5,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4),(5,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4),(5,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,5),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5),(4,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5),(5,5)]]
    let c10r1982choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1982targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)] c10r1982choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1982targets, c10r1982choice, ?_, checked⟩
    intro S h
    simp only [c10r1982targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 28 _ (by rfl)
  have c10r1983_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)] := by
    let c10r1983targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4),(6,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4),(6,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4),(6,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4),(6,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,5),(4,5),(5,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(5,3),(5,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4),(5,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4),(6,4)]]
    let c10r1983choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 5) then (16,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r1983targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)] c10r1983choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1983targets, c10r1983choice, ?_, checked⟩
    intro S h
    simp only [c10r1983targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,true,false,false,true,true] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1976_closed
  · subst row; exact c10r1977_closed
  · subst row; exact c10r1978_closed
  · subst row; exact c10r1979_closed
  · subst row; exact c10r1980_closed
  · subst row; exact c10r1981_closed
  · subst row; exact c10r1982_closed
  · subst row; exact c10r1983_closed
theorem C10R01952_closed (row : List GridPoint) (h : FamilyMember row F10B000L61) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L61, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R01952G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01952G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01952G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01952G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01952G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01952G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01952G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01952G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01952G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01952G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01952G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01952G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01952G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01952G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01952G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01952G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01952G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01952G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01952G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01952G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01952G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01952G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01952G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01952G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01952G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01952G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01952G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01952G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01952G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01952G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01952G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01952G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
