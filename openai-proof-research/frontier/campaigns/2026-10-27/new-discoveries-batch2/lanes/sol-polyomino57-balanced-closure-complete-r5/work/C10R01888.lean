import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R01888G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1888_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)] := by
    let c10r1888targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(3,3)]]
    let c10r1888choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r1888targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)] c10r1888choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1888targets, c10r1888choice, ?_, checked⟩
    intro S h
    simp only [c10r1888targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 30 _ (by rfl)
  have c10r1889_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)] := by
    let c10r1889targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(3,4)]]
    let c10r1889choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1889targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)] c10r1889choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1889targets, c10r1889choice, ?_, checked⟩
    intro S h
    simp only [c10r1889targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 2 _ (by rfl)
  have c10r1890_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)] := by
    let c10r1890targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5),(3,5)]]
    let c10r1890choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1890targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)] c10r1890choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1890targets, c10r1890choice, ?_, checked⟩
    intro S h
    simp only [c10r1890targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 5 _ (by rfl)
  have c10r1891_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)] := by
    let c10r1891targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6),(3,6)]]
    let c10r1891choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1891targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)] c10r1891choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1891targets, c10r1891choice, ?_, checked⟩
    intro S h
    simp only [c10r1891targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 7 _ (by rfl)
  have c10r1892_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)] := by
    let c10r1892targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7),(3,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7),(2,8)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7),(3,7)]]
    let c10r1892choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 8) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 8) then (16,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 7) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r1892targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)] c10r1892choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1892targets, c10r1892choice, ?_, checked⟩
    intro S h
    simp only [c10r1892targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 9 _ (by rfl)
  have c10r1893_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)] := by
    let c10r1893targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,3)]]
    let c10r1893choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1893targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)] c10r1893choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1893targets, c10r1893choice, ?_, checked⟩
    intro S h
    simp only [c10r1893targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
  have c10r1894_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)] := by
    let c10r1894targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(3,4)]]
    let c10r1894choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1894targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)] c10r1894choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1894targets, c10r1894choice, ?_, checked⟩
    intro S h
    simp only [c10r1894targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
  have c10r1895_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)] := by
    let c10r1895targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(3,5)]]
    let c10r1895choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1895targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)] c10r1895choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1895targets, c10r1895choice, ?_, checked⟩
    intro S h
    simp only [c10r1895targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1888_closed
  · subst row; exact c10r1889_closed
  · subst row; exact c10r1890_closed
  · subst row; exact c10r1891_closed
  · subst row; exact c10r1892_closed
  · subst row; exact c10r1893_closed
  · subst row; exact c10r1894_closed
  · subst row; exact c10r1895_closed
theorem C10R01888G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1896_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)] := by
    let c10r1896targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,4),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6),(3,6)]]
    let c10r1896choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1896targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)] c10r1896choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1896targets, c10r1896choice, ?_, checked⟩
    intro S h
    simp only [c10r1896targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 25 _ (by rfl)
  have c10r1897_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)] := by
    let c10r1897targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3),(4,3)]]
    let c10r1897choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r1897targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)] c10r1897choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1897targets, c10r1897choice, ?_, checked⟩
    intro S h
    simp only [c10r1897targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 28 _ (by rfl)
  have c10r1898_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)] := by
    let c10r1898targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(3,5)]]
    let c10r1898choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1898targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)] c10r1898choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1898targets, c10r1898choice, ?_, checked⟩
    intro S h
    simp only [c10r1898targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 31 _ (by rfl)
  have c10r1899_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)] := by
    let c10r1899targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,5),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6),(3,6)]]
    let c10r1899choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1899targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)] c10r1899choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1899targets, c10r1899choice, ?_, checked⟩
    intro S h
    simp only [c10r1899targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
  have c10r1900_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)] := by
    let c10r1900targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4),(4,4)]]
    let c10r1900choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1900targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)] c10r1900choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1900targets, c10r1900choice, ?_, checked⟩
    intro S h
    simp only [c10r1900targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 5 _ (by rfl)
  have c10r1901_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)] := by
    let c10r1901targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6),(3,6)]]
    let c10r1901choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1901targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)] c10r1901choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1901targets, c10r1901choice, ?_, checked⟩
    intro S h
    simp only [c10r1901targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
  have c10r1902_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)] := by
    let c10r1902targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5),(4,5)]]
    let c10r1902choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1902targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)] c10r1902choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1902targets, c10r1902choice, ?_, checked⟩
    intro S h
    simp only [c10r1902targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 11 _ (by rfl)
  have c10r1903_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)] := by
    let c10r1903targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6),(3,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6),(3,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6),(3,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,7),(2,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7),(2,8)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7),(3,7)]]
    let c10r1903choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 8) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 7) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1903targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)] c10r1903choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1903targets, c10r1903choice, ?_, checked⟩
    intro S h
    simp only [c10r1903targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1896_closed
  · subst row; exact c10r1897_closed
  · subst row; exact c10r1898_closed
  · subst row; exact c10r1899_closed
  · subst row; exact c10r1900_closed
  · subst row; exact c10r1901_closed
  · subst row; exact c10r1902_closed
  · subst row; exact c10r1903_closed
theorem C10R01888G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1904_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)] := by
    let c10r1904targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6),(4,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6),(4,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6),(4,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6),(4,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7),(2,7),(3,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6),(3,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6),(4,6)]]
    let c10r1904choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 7) then (16,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 6) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r1904targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)] c10r1904choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1904targets, c10r1904choice, ?_, checked⟩
    intro S h
    simp only [c10r1904targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 17 _ (by rfl)
  have c10r1905_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)] := by
    let c10r1905targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,3)]]
    let c10r1905choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1905targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)] c10r1905choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1905targets, c10r1905choice, ?_, checked⟩
    intro S h
    simp only [c10r1905targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 24 _ (by rfl)
  have c10r1906_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)] := by
    let c10r1906targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,4)]]
    let c10r1906choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1906targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)] c10r1906choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1906targets, c10r1906choice, ?_, checked⟩
    intro S h
    simp only [c10r1906targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 28 _ (by rfl)
  have c10r1907_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)] := by
    let c10r1907targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,3),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,5)]]
    let c10r1907choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1907targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)] c10r1907choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1907targets, c10r1907choice, ?_, checked⟩
    intro S h
    simp only [c10r1907targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 0 _ (by rfl)
  have c10r1908_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)] := by
    let c10r1908targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2),(4,2)]]
    let c10r1908choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1908targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)] c10r1908choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1908targets, c10r1908choice, ?_, checked⟩
    intro S h
    simp only [c10r1908targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 3 _ (by rfl)
  have c10r1909_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)] := by
    let c10r1909targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3),(4,3)]]
    let c10r1909choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1909targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)] c10r1909choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1909targets, c10r1909choice, ?_, checked⟩
    intro S h
    simp only [c10r1909targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 5 _ (by rfl)
  have c10r1910_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)] := by
    let c10r1910targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,5)]]
    let c10r1910choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1910targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)] c10r1910choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1910targets, c10r1910choice, ?_, checked⟩
    intro S h
    simp only [c10r1910targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 9 _ (by rfl)
  have c10r1911_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)] := by
    let c10r1911targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3),(4,3)]]
    let c10r1911choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1911targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)] c10r1911choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1911targets, c10r1911choice, ?_, checked⟩
    intro S h
    simp only [c10r1911targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1904_closed
  · subst row; exact c10r1905_closed
  · subst row; exact c10r1906_closed
  · subst row; exact c10r1907_closed
  · subst row; exact c10r1908_closed
  · subst row; exact c10r1909_closed
  · subst row; exact c10r1910_closed
  · subst row; exact c10r1911_closed
theorem C10R01888G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1912_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)] := by
    let c10r1912targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4),(4,4)]]
    let c10r1912choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1912targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)] c10r1912choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1912targets, c10r1912choice, ?_, checked⟩
    intro S h
    simp only [c10r1912targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 14 _ (by rfl)
  have c10r1913_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)] := by
    let c10r1913targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6),(3,6)]]
    let c10r1913choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1913targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)] c10r1913choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1913targets, c10r1913choice, ?_, checked⟩
    intro S h
    simp only [c10r1913targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 18 _ (by rfl)
  have c10r1914_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)] := by
    let c10r1914targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3),(4,3)]]
    let c10r1914choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1914targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)] c10r1914choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1914targets, c10r1914choice, ?_, checked⟩
    intro S h
    simp only [c10r1914targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 22 _ (by rfl)
  have c10r1915_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)] := by
    let c10r1915targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5),(4,5)]]
    let c10r1915choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1915targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)] c10r1915choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1915targets, c10r1915choice, ?_, checked⟩
    intro S h
    simp only [c10r1915targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 25 _ (by rfl)
  have c10r1916_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)] := by
    let c10r1916targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(4,3)]]
    let c10r1916choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1916targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)] c10r1916choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1916targets, c10r1916choice, ?_, checked⟩
    intro S h
    simp only [c10r1916targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 29 _ (by rfl)
  have c10r1917_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)] := by
    let c10r1917targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4),(4,4)]]
    let c10r1917choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c10r1917targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)] c10r1917choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1917targets, c10r1917choice, ?_, checked⟩
    intro S h
    simp only [c10r1917targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 0 _ (by rfl)
  have c10r1918_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)] := by
    let c10r1918targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3),(5,3)]]
    let c10r1918choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (16,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c10r1918targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)] c10r1918choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1918targets, c10r1918choice, ?_, checked⟩
    intro S h
    simp only [c10r1918targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 3 _ (by rfl)
  have c10r1919_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)] := by
    let c10r1919targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6),(3,6)]]
    let c10r1919choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1919targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)] c10r1919choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1919targets, c10r1919choice, ?_, checked⟩
    intro S h
    simp only [c10r1919targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,true,false,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,true,false,false,true,true,false,true] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1912_closed
  · subst row; exact c10r1913_closed
  · subst row; exact c10r1914_closed
  · subst row; exact c10r1915_closed
  · subst row; exact c10r1916_closed
  · subst row; exact c10r1917_closed
  · subst row; exact c10r1918_closed
  · subst row; exact c10r1919_closed
theorem C10R01888_closed (row : List GridPoint) (h : FamilyMember row F10B000L59) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L59, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R01888G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01888G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01888G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01888G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01888G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01888G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01888G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01888G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01888G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01888G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01888G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01888G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01888G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01888G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01888G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01888G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01888G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01888G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01888G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01888G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01888G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01888G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01888G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01888G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01888G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01888G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01888G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01888G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01888G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01888G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01888G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01888G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
