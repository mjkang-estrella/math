import Lean
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R02144G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2144_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)] := by
    let c9r2144targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)]]
    let c9r2144choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2144targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)] c9r2144choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2144targets, c9r2144choice, ?_, checked⟩
    intro S h
    simp only [c9r2144targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 4 _ (by rfl)
  have c9r2145_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)] := by
    let c9r2145targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)]]
    let c9r2145choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,5),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2145targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)] c9r2145choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2145targets, c9r2145choice, ?_, checked⟩
    intro S h
    simp only [c9r2145targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 7 _ (by rfl)
  have c9r2146_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)] := by
    let c9r2146targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)]]
    let c9r2146choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2146targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)] c9r2146choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2146targets, c9r2146choice, ?_, checked⟩
    intro S h
    simp only [c9r2146targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 10 _ (by rfl)
  have c9r2147_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)] := by
    let c9r2147targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]]
    let c9r2147choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,5),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2147targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)] c9r2147choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2147targets, c9r2147choice, ?_, checked⟩
    intro S h
    simp only [c9r2147targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
  have c9r2148_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)] := by
    let c9r2148targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)]]
    let c9r2148choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2148targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)] c9r2148choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2148targets, c9r2148choice, ?_, checked⟩
    intro S h
    simp only [c9r2148targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 16 _ (by rfl)
  have c9r2149_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)] := by
    let c9r2149targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)]]
    let c9r2149choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,6),(13,(0,0))),((4,4),(14,(0,0))),((4,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2149targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)] c9r2149choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2149targets, c9r2149choice, ?_, checked⟩
    intro S h
    simp only [c9r2149targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 19 _ (by rfl)
  have c9r2150_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)] := by
    let c9r2150targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)]]
    let c9r2150choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,5),(13,(0,0))),((4,3),(14,(0,0))),((4,5),(15,(0,0))),((5,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2150targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)] c9r2150choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2150targets, c9r2150choice, ?_, checked⟩
    intro S h
    simp only [c9r2150targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 22 _ (by rfl)
  have c9r2151_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r2151targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r2151choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2151targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r2151choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2151targets, c9r2151choice, ?_, checked⟩
    intro S h
    simp only [c9r2151targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2144_closed
  · subst row; exact c9r2145_closed
  · subst row; exact c9r2146_closed
  · subst row; exact c9r2147_closed
  · subst row; exact c9r2148_closed
  · subst row; exact c9r2149_closed
  · subst row; exact c9r2150_closed
  · subst row; exact c9r2151_closed
theorem C9R02144G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2152_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] := by
    let c9r2152targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)]]
    let c9r2152choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2152targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] c9r2152choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2152targets, c9r2152choice, ?_, checked⟩
    intro S h
    simp only [c9r2152targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 31 _ (by rfl)
  have c9r2153_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] := by
    let c9r2153targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)]]
    let c9r2153choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2153targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] c9r2153choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2153targets, c9r2153choice, ?_, checked⟩
    intro S h
    simp only [c9r2153targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 1 _ (by rfl)
  have c9r2154_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] := by
    let c9r2154targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)]]
    let c9r2154choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2154targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] c9r2154choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2154targets, c9r2154choice, ?_, checked⟩
    intro S h
    simp only [c9r2154targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 3 _ (by rfl)
  have c9r2155_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r2155targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r2155choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2155targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)] c9r2155choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2155targets, c9r2155choice, ?_, checked⟩
    intro S h
    simp only [c9r2155targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 7 _ (by rfl)
  have c9r2156_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)] := by
    let c9r2156targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)]]
    let c9r2156choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2156targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)] c9r2156choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2156targets, c9r2156choice, ?_, checked⟩
    intro S h
    simp only [c9r2156targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 10 _ (by rfl)
  have c9r2157_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)] := by
    let c9r2157targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)]]
    let c9r2157choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2157targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)] c9r2157choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2157targets, c9r2157choice, ?_, checked⟩
    intro S h
    simp only [c9r2157targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 12 _ (by rfl)
  have c9r2158_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)] := by
    let c9r2158targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,4)]]
    let c9r2158choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,5),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2158targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)] c9r2158choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2158targets, c9r2158choice, ?_, checked⟩
    intro S h
    simp only [c9r2158targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 16 _ (by rfl)
  have c9r2159_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)] := by
    let c9r2159targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(5,1)]]
    let c9r2159choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2159targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)] c9r2159choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2159targets, c9r2159choice, ?_, checked⟩
    intro S h
    simp only [c9r2159targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2152_closed
  · subst row; exact c9r2153_closed
  · subst row; exact c9r2154_closed
  · subst row; exact c9r2155_closed
  · subst row; exact c9r2156_closed
  · subst row; exact c9r2157_closed
  · subst row; exact c9r2158_closed
  · subst row; exact c9r2159_closed
theorem C9R02144G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2160_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)] := by
    let c9r2160targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(5,3)]]
    let c9r2160choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2160targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)] c9r2160choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2160targets, c9r2160choice, ?_, checked⟩
    intro S h
    simp only [c9r2160targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 23 _ (by rfl)
  have c9r2161_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] := by
    let c9r2161targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)]]
    let c9r2161choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,-1),(12,(0,1))),((4,2),(13,(0,0))),((5,0),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2161targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] c9r2161choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2161targets, c9r2161choice, ?_, checked⟩
    intro S h
    simp only [c9r2161targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 26 _ (by rfl)
  have c9r2162_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)] := by
    let c9r2162targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,2)]]
    let c9r2162choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2162targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)] c9r2162choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2162targets, c9r2162choice, ?_, checked⟩
    intro S h
    simp only [c9r2162targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 29 _ (by rfl)
  have c9r2163_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)] := by
    let c9r2163targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(6,1)]]
    let c9r2163choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,0),(14,(0,0))),((5,2),(15,(0,0))),((6,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2163targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)] c9r2163choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2163targets, c9r2163choice, ?_, checked⟩
    intro S h
    simp only [c9r2163targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 0 _ (by rfl)
  have c9r2164_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)] := by
    let c9r2164targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)]]
    let c9r2164choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2164targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)] c9r2164choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2164targets, c9r2164choice, ?_, checked⟩
    intro S h
    simp only [c9r2164targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 4 _ (by rfl)
  have c9r2165_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)] := by
    let c9r2165targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)]]
    let c9r2165choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2165targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)] c9r2165choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2165targets, c9r2165choice, ?_, checked⟩
    intro S h
    simp only [c9r2165targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 7 _ (by rfl)
  have c9r2166_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)] := by
    let c9r2166targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)]]
    let c9r2166choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2166targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)] c9r2166choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2166targets, c9r2166choice, ?_, checked⟩
    intro S h
    simp only [c9r2166targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 9 _ (by rfl)
  have c9r2167_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)] := by
    let c9r2167targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)]]
    let c9r2167choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2167targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)] c9r2167choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2167targets, c9r2167choice, ?_, checked⟩
    intro S h
    simp only [c9r2167targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2160_closed
  · subst row; exact c9r2161_closed
  · subst row; exact c9r2162_closed
  · subst row; exact c9r2163_closed
  · subst row; exact c9r2164_closed
  · subst row; exact c9r2165_closed
  · subst row; exact c9r2166_closed
  · subst row; exact c9r2167_closed
theorem C9R02144G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2168_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)] := by
    let c9r2168targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)]]
    let c9r2168choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,4),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2168targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)] c9r2168choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2168targets, c9r2168choice, ?_, checked⟩
    intro S h
    simp only [c9r2168targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 16 _ (by rfl)
  have c9r2169_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)] := by
    let c9r2169targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)]]
    let c9r2169choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2169targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)] c9r2169choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2169targets, c9r2169choice, ?_, checked⟩
    intro S h
    simp only [c9r2169targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 19 _ (by rfl)
  have c9r2170_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)] := by
    let c9r2170targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)]]
    let c9r2170choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,6),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0))),((4,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2170targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)] c9r2170choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2170targets, c9r2170choice, ?_, checked⟩
    intro S h
    simp only [c9r2170targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 23 _ (by rfl)
  have c9r2171_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)] := by
    let c9r2171targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)]]
    let c9r2171choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,5),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2171targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)] c9r2171choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2171targets, c9r2171choice, ?_, checked⟩
    intro S h
    simp only [c9r2171targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 26 _ (by rfl)
  have c9r2172_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)] := by
    let c9r2172targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)]]
    let c9r2172choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,5),(11,(0,0))),((4,3),(12,(0,0))),((4,5),(13,(0,0))),((5,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2172targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)] c9r2172choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2172targets, c9r2172choice, ?_, checked⟩
    intro S h
    simp only [c9r2172targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 28 _ (by rfl)
  have c9r2173_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)] := by
    let c9r2173targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)]]
    let c9r2173choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,4),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2173targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)] c9r2173choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2173targets, c9r2173choice, ?_, checked⟩
    intro S h
    simp only [c9r2173targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 0 _ (by rfl)
  have c9r2174_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)] := by
    let c9r2174targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)]]
    let c9r2174choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,5),(13,(0,0))),((5,3),(14,(0,0))),((5,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2174targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)] c9r2174choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2174targets, c9r2174choice, ?_, checked⟩
    intro S h
    simp only [c9r2174targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 3 _ (by rfl)
  have c9r2175_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)] := by
    let c9r2175targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)]]
    let c9r2175choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,2),(14,(0,0))),((5,4),(15,(0,0))),((6,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2175targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)] c9r2175choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2175targets, c9r2175choice, ?_, checked⟩
    intro S h
    simp only [c9r2175targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2168_closed
  · subst row; exact c9r2169_closed
  · subst row; exact c9r2170_closed
  · subst row; exact c9r2171_closed
  · subst row; exact c9r2172_closed
  · subst row; exact c9r2173_closed
  · subst row; exact c9r2174_closed
  · subst row; exact c9r2175_closed
theorem C9R02144_closed (row : List GridPoint) (h : FamilyMember row F9B001L3) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L3, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R02144G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02144G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02144G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02144G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02144G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02144G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02144G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02144G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02144G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02144G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02144G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02144G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02144G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02144G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02144G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02144G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02144G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02144G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02144G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02144G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02144G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02144G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02144G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02144G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02144G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02144G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02144G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02144G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02144G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02144G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02144G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02144G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
