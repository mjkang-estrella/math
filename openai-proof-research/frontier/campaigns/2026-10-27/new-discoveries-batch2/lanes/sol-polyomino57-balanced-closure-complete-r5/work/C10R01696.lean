import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R01696G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1696_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)] := by
    let c10r1696targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4)]]
    let c10r1696choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1696targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)] c10r1696choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1696targets, c10r1696choice, ?_, checked⟩
    intro S h
    simp only [c10r1696targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 19 _ (by rfl)
  have c10r1697_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)] := by
    let c10r1697targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(3,6)]]
    let c10r1697choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1697targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)] c10r1697choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1697targets, c10r1697choice, ?_, checked⟩
    intro S h
    simp only [c10r1697targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 22 _ (by rfl)
  have c10r1698_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)] := by
    let c10r1698targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5),(4,5)]]
    let c10r1698choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1698targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)] c10r1698choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1698targets, c10r1698choice, ?_, checked⟩
    intro S h
    simp only [c10r1698targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 25 _ (by rfl)
  have c10r1699_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c10r1699targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c10r1699choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1699targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c10r1699choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1699targets, c10r1699choice, ?_, checked⟩
    intro S h
    simp only [c10r1699targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 31 _ (by rfl)
  have c10r1700_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)] := by
    let c10r1700targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)]]
    let c10r1700choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1700targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)] c10r1700choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1700targets, c10r1700choice, ?_, checked⟩
    intro S h
    simp only [c10r1700targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 3 _ (by rfl)
  have c10r1701_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)] := by
    let c10r1701targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,4)]]
    let c10r1701choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1701targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)] c10r1701choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1701targets, c10r1701choice, ?_, checked⟩
    intro S h
    simp only [c10r1701targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 7 _ (by rfl)
  have c10r1702_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)] := by
    let c10r1702targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1)]]
    let c10r1702choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1702targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)] c10r1702choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1702targets, c10r1702choice, ?_, checked⟩
    intro S h
    simp only [c10r1702targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 10 _ (by rfl)
  have c10r1703_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)] := by
    let c10r1703targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(4,2)]]
    let c10r1703choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1703targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)] c10r1703choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1703targets, c10r1703choice, ?_, checked⟩
    intro S h
    simp only [c10r1703targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1696_closed
  · subst row; exact c10r1697_closed
  · subst row; exact c10r1698_closed
  · subst row; exact c10r1699_closed
  · subst row; exact c10r1700_closed
  · subst row; exact c10r1701_closed
  · subst row; exact c10r1702_closed
  · subst row; exact c10r1703_closed
theorem C10R01696G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1704_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)] := by
    let c10r1704targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)]]
    let c10r1704choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1704targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)] c10r1704choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1704targets, c10r1704choice, ?_, checked⟩
    intro S h
    simp only [c10r1704targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 16 _ (by rfl)
  have c10r1705_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)] := by
    let c10r1705targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)]]
    let c10r1705choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1705targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)] c10r1705choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1705targets, c10r1705choice, ?_, checked⟩
    intro S h
    simp only [c10r1705targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 19 _ (by rfl)
  have c10r1706_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)] := by
    let c10r1706targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)]]
    let c10r1706choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1706targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)] c10r1706choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1706targets, c10r1706choice, ?_, checked⟩
    intro S h
    simp only [c10r1706targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 21 _ (by rfl)
  have c10r1707_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)] := by
    let c10r1707targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)]]
    let c10r1707choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1707targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)] c10r1707choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1707targets, c10r1707choice, ?_, checked⟩
    intro S h
    simp only [c10r1707targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 25 _ (by rfl)
  have c10r1708_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)] := by
    let c10r1708targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)]]
    let c10r1708choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1708targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)] c10r1708choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1708targets, c10r1708choice, ?_, checked⟩
    intro S h
    simp only [c10r1708targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 29 _ (by rfl)
  have c10r1709_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)] := by
    let c10r1709targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)]]
    let c10r1709choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1709targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)] c10r1709choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1709targets, c10r1709choice, ?_, checked⟩
    intro S h
    simp only [c10r1709targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 0 _ (by rfl)
  have c10r1710_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)] := by
    let c10r1710targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)]]
    let c10r1710choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1710targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)] c10r1710choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1710targets, c10r1710choice, ?_, checked⟩
    intro S h
    simp only [c10r1710targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 4 _ (by rfl)
  have c10r1711_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)] := by
    let c10r1711targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)]]
    let c10r1711choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1711targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)] c10r1711choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1711targets, c10r1711choice, ?_, checked⟩
    intro S h
    simp only [c10r1711targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1704_closed
  · subst row; exact c10r1705_closed
  · subst row; exact c10r1706_closed
  · subst row; exact c10r1707_closed
  · subst row; exact c10r1708_closed
  · subst row; exact c10r1709_closed
  · subst row; exact c10r1710_closed
  · subst row; exact c10r1711_closed
theorem C10R01696G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1712_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)] := by
    let c10r1712targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)]]
    let c10r1712choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1712targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)] c10r1712choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1712targets, c10r1712choice, ?_, checked⟩
    intro S h
    simp only [c10r1712targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 10 _ (by rfl)
  have c10r1713_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)] := by
    let c10r1713targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)]]
    let c10r1713choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1713targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)] c10r1713choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1713targets, c10r1713choice, ?_, checked⟩
    intro S h
    simp only [c10r1713targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 14 _ (by rfl)
  have c10r1714_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)] := by
    let c10r1714targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)]]
    let c10r1714choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1714targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)] c10r1714choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1714targets, c10r1714choice, ?_, checked⟩
    intro S h
    simp only [c10r1714targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 17 _ (by rfl)
  have c10r1715_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)] := by
    let c10r1715targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)]]
    let c10r1715choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c10r1715targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)] c10r1715choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1715targets, c10r1715choice, ?_, checked⟩
    intro S h
    simp only [c10r1715targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 19 _ (by rfl)
  have c10r1716_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)] := by
    let c10r1716targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)]]
    let c10r1716choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1716targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)] c10r1716choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1716targets, c10r1716choice, ?_, checked⟩
    intro S h
    simp only [c10r1716targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 23 _ (by rfl)
  have c10r1717_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)] := by
    let c10r1717targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,4)]]
    let c10r1717choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1717targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)] c10r1717choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1717targets, c10r1717choice, ?_, checked⟩
    intro S h
    simp only [c10r1717targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 26 _ (by rfl)
  have c10r1718_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)] := by
    let c10r1718targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3),(5,3)]]
    let c10r1718choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1718targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)] c10r1718choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1718targets, c10r1718choice, ?_, checked⟩
    intro S h
    simp only [c10r1718targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 29 _ (by rfl)
  have c10r1719_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)] := by
    let c10r1719targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,6)]]
    let c10r1719choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1719targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)] c10r1719choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1719targets, c10r1719choice, ?_, checked⟩
    intro S h
    simp only [c10r1719targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1712_closed
  · subst row; exact c10r1713_closed
  · subst row; exact c10r1714_closed
  · subst row; exact c10r1715_closed
  · subst row; exact c10r1716_closed
  · subst row; exact c10r1717_closed
  · subst row; exact c10r1718_closed
  · subst row; exact c10r1719_closed
theorem C10R01696G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r1720_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)] := by
    let c10r1720targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)]]
    let c10r1720choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1720targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)] c10r1720choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1720targets, c10r1720choice, ?_, checked⟩
    intro S h
    simp only [c10r1720targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 4 _ (by rfl)
  have c10r1721_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)] := by
    let c10r1721targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5),(4,5)]]
    let c10r1721choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1721targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)] c10r1721choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1721targets, c10r1721choice, ?_, checked⟩
    intro S h
    simp only [c10r1721targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 6 _ (by rfl)
  have c10r1722_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)] := by
    let c10r1722targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)]]
    let c10r1722choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1722targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)] c10r1722choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1722targets, c10r1722choice, ?_, checked⟩
    intro S h
    simp only [c10r1722targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 10 _ (by rfl)
  have c10r1723_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)] := by
    let c10r1723targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,5)]]
    let c10r1723choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1723targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)] c10r1723choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1723targets, c10r1723choice, ?_, checked⟩
    intro S h
    simp only [c10r1723targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 13 _ (by rfl)
  have c10r1724_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)] := by
    let c10r1724targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4),(5,4)]]
    let c10r1724choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c10r1724targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4),(4,4)] c10r1724choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1724targets, c10r1724choice, ?_, checked⟩
    intro S h
    simp only [c10r1724targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 16 _ (by rfl)
  have c10r1725_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)] := by
    let c10r1725targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,6),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(1,6),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,5)]]
    let c10r1725choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c10r1725targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)] c10r1725choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1725targets, c10r1725choice, ?_, checked⟩
    intro S h
    simp only [c10r1725targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 22 _ (by rfl)
  have c10r1726_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c10r1726targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c10r1726choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1726targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c10r1726choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1726targets, c10r1726choice, ?_, checked⟩
    intro S h
    simp only [c10r1726targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 28 _ (by rfl)
  have c10r1727_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c10r1727targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c10r1727choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 1) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (3,(1,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c10r1727targets [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c10r1727choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c10r1727targets, c10r1727choice, ?_, checked⟩
    intro S h
    simp only [c10r1727targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family11 [false,true,false,false,false,false,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,true,true,true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,false,true,false,true,false,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [true,true,false,false,true,true,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,true,false,true,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family11 [false,false,false,false,true,false,true,true,true,false,false,false] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r1720_closed
  · subst row; exact c10r1721_closed
  · subst row; exact c10r1722_closed
  · subst row; exact c10r1723_closed
  · subst row; exact c10r1724_closed
  · subst row; exact c10r1725_closed
  · subst row; exact c10r1726_closed
  · subst row; exact c10r1727_closed
theorem C10R01696_closed (row : List GridPoint) (h : FamilyMember row F10B000L53) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L53, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R01696G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01696G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01696G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01696G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01696G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01696G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01696G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01696G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01696G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01696G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01696G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01696G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01696G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01696G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01696G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01696G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01696G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01696G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01696G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01696G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01696G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01696G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01696G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01696G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R01696G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R01696G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R01696G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R01696G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R01696G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R01696G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R01696G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R01696G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
