import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R02240G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2240_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r2240targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r2240choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2240targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r2240choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2240targets, c9r2240choice, ?_, checked⟩
    intro S h
    simp only [c9r2240targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 0 _ (by rfl)
  have c9r2241_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r2241targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r2241choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2241targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)] c9r2241choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2241targets, c9r2241choice, ?_, checked⟩
    intro S h
    simp only [c9r2241targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 5 _ (by rfl)
  have c9r2242_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r2242targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r2242choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2242targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)] c9r2242choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2242targets, c9r2242choice, ?_, checked⟩
    intro S h
    simp only [c9r2242targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 7 _ (by rfl)
  have c9r2243_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r2243targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r2243choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2243targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)] c9r2243choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2243targets, c9r2243choice, ?_, checked⟩
    intro S h
    simp only [c9r2243targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 9 _ (by rfl)
  have c9r2244_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)] := by
    let c9r2244targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)]]
    let c9r2244choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2244targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)] c9r2244choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2244targets, c9r2244choice, ?_, checked⟩
    intro S h
    simp only [c9r2244targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 12 _ (by rfl)
  have c9r2245_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)] := by
    let c9r2245targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)]]
    let c9r2245choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,-1),(14,(0,1))),((6,1),(15,(0,0))),((7,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2245targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)] c9r2245choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2245targets, c9r2245choice, ?_, checked⟩
    intro S h
    simp only [c9r2245targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 14 _ (by rfl)
  have c9r2246_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r2246targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r2246choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2246targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)] c9r2246choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2246targets, c9r2246choice, ?_, checked⟩
    intro S h
    simp only [c9r2246targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 18 _ (by rfl)
  have c9r2247_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r2247targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r2247choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2247targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)] c9r2247choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2247targets, c9r2247choice, ?_, checked⟩
    intro S h
    simp only [c9r2247targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2240_closed
  · subst row; exact c9r2241_closed
  · subst row; exact c9r2242_closed
  · subst row; exact c9r2243_closed
  · subst row; exact c9r2244_closed
  · subst row; exact c9r2245_closed
  · subst row; exact c9r2246_closed
  · subst row; exact c9r2247_closed
theorem C9R02240G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2248_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r2248targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r2248choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2248targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)] c9r2248choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2248targets, c9r2248choice, ?_, checked⟩
    intro S h
    simp only [c9r2248targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 23 _ (by rfl)
  have c9r2249_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r2249targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r2249choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2249targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)] c9r2249choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2249targets, c9r2249choice, ?_, checked⟩
    intro S h
    simp only [c9r2249targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 26 _ (by rfl)
  have c9r2250_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r2250targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r2250choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2250targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)] c9r2250choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2250targets, c9r2250choice, ?_, checked⟩
    intro S h
    simp only [c9r2250targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 29 _ (by rfl)
  have c9r2251_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r2251targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r2251choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2251targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)] c9r2251choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2251targets, c9r2251choice, ?_, checked⟩
    intro S h
    simp only [c9r2251targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 0 _ (by rfl)
  have c9r2252_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r2252targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,5),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r2252choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((2,5),(10,(0,0))),((3,0),(11,(0,0))),((3,6),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0))),((4,4),(16,(0,0))),((4,5),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2252targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)] c9r2252choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2252targets, c9r2252choice, ?_, checked⟩
    intro S h
    simp only [c9r2252targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 6 _ (by rfl)
  have c9r2253_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)] := by
    let c9r2253targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)]]
    let c9r2253choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,5),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((4,4),(15,(0,0))),((5,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2253targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)] c9r2253choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2253targets, c9r2253choice, ?_, checked⟩
    intro S h
    simp only [c9r2253targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 11 _ (by rfl)
  have c9r2254_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r2254targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r2254choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,5),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2254targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)] c9r2254choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2254targets, c9r2254choice, ?_, checked⟩
    intro S h
    simp only [c9r2254targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 14 _ (by rfl)
  have c9r2255_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r2255targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r2255choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,5),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,4),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2255targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)] c9r2255choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2255targets, c9r2255choice, ?_, checked⟩
    intro S h
    simp only [c9r2255targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2248_closed
  · subst row; exact c9r2249_closed
  · subst row; exact c9r2250_closed
  · subst row; exact c9r2251_closed
  · subst row; exact c9r2252_closed
  · subst row; exact c9r2253_closed
  · subst row; exact c9r2254_closed
  · subst row; exact c9r2255_closed
theorem C9R02240G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2256_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r2256targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r2256choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,5),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((4,5),(15,(0,0))),((5,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2256targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)] c9r2256choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2256targets, c9r2256choice, ?_, checked⟩
    intro S h
    simp only [c9r2256targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 18 _ (by rfl)
  have c9r2257_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r2257targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r2257choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((5,0),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2257targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r2257choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2257targets, c9r2257choice, ?_, checked⟩
    intro S h
    simp only [c9r2257targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 22 _ (by rfl)
  have c9r2258_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r2258targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r2258choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2258targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)] c9r2258choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2258targets, c9r2258choice, ?_, checked⟩
    intro S h
    simp only [c9r2258targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 25 _ (by rfl)
  have c9r2259_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)] := by
    let c9r2259targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)]]
    let c9r2259choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,1),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2259targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)] c9r2259choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2259targets, c9r2259choice, ?_, checked⟩
    intro S h
    simp only [c9r2259targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 28 _ (by rfl)
  have c9r2260_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)] := by
    let c9r2260targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)]]
    let c9r2260choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((5,0),(14,(0,0))),((5,2),(15,(0,0))),((6,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2260targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)] c9r2260choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2260targets, c9r2260choice, ?_, checked⟩
    intro S h
    simp only [c9r2260targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 31 _ (by rfl)
  have c9r2261_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)] := by
    let c9r2261targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)]]
    let c9r2261choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,4),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2261targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)] c9r2261choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2261targets, c9r2261choice, ?_, checked⟩
    intro S h
    simp only [c9r2261targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 2 _ (by rfl)
  have c9r2262_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)] := by
    let c9r2262targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)]]
    let c9r2262choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2262targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)] c9r2262choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2262targets, c9r2262choice, ?_, checked⟩
    intro S h
    simp only [c9r2262targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 5 _ (by rfl)
  have c9r2263_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)] := by
    let c9r2263targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(5,4)]]
    let c9r2263choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,5),(13,(0,0))),((5,3),(14,(0,0))),((5,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2263targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)] c9r2263choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2263targets, c9r2263choice, ?_, checked⟩
    intro S h
    simp only [c9r2263targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2256_closed
  · subst row; exact c9r2257_closed
  · subst row; exact c9r2258_closed
  · subst row; exact c9r2259_closed
  · subst row; exact c9r2260_closed
  · subst row; exact c9r2261_closed
  · subst row; exact c9r2262_closed
  · subst row; exact c9r2263_closed
theorem C9R02240G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2264_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)] := by
    let c9r2264targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3),(6,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3),(6,3)]]
    let c9r2264choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,2),(14,(0,0))),((5,4),(15,(0,0))),((6,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2264targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)] c9r2264choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2264targets, c9r2264choice, ?_, checked⟩
    intro S h
    simp only [c9r2264targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 11 _ (by rfl)
  have c9r2265_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r2265targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r2265choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2265targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)] c9r2265choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2265targets, c9r2265choice, ?_, checked⟩
    intro S h
    simp only [c9r2265targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 16 _ (by rfl)
  have c9r2266_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c9r2266targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c9r2266choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2266targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)] c9r2266choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2266targets, c9r2266choice, ?_, checked⟩
    intro S h
    simp only [c9r2266targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 18 _ (by rfl)
  have c9r2267_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c9r2267targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c9r2267choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2267targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)] c9r2267choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2267targets, c9r2267choice, ?_, checked⟩
    intro S h
    simp only [c9r2267targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 20 _ (by rfl)
  have c9r2268_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)] := by
    let c9r2268targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)]]
    let c9r2268choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,4),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2268targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)] c9r2268choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2268targets, c9r2268choice, ?_, checked⟩
    intro S h
    simp only [c9r2268targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 24 _ (by rfl)
  have c9r2269_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)] := by
    let c9r2269targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)]]
    let c9r2269choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2269targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)] c9r2269choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2269targets, c9r2269choice, ?_, checked⟩
    intro S h
    simp only [c9r2269targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 27 _ (by rfl)
  have c9r2270_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)] := by
    let c9r2270targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)]]
    let c9r2270choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2270targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)] c9r2270choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2270targets, c9r2270choice, ?_, checked⟩
    intro S h
    simp only [c9r2270targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 29 _ (by rfl)
  have c9r2271_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)] := by
    let c9r2271targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)]]
    let c9r2271choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2271targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)] c9r2271choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2271targets, c9r2271choice, ?_, checked⟩
    intro S h
    simp only [c9r2271targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2264_closed
  · subst row; exact c9r2265_closed
  · subst row; exact c9r2266_closed
  · subst row; exact c9r2267_closed
  · subst row; exact c9r2268_closed
  · subst row; exact c9r2269_closed
  · subst row; exact c9r2270_closed
  · subst row; exact c9r2271_closed
theorem C9R02240_closed (row : List GridPoint) (h : FamilyMember row F9B001L6) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L6, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R02240G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02240G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02240G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02240G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02240G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02240G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02240G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02240G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02240G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02240G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02240G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02240G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02240G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02240G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02240G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02240G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02240G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02240G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02240G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02240G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02240G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02240G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02240G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02240G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02240G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02240G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02240G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02240G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02240G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02240G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02240G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02240G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
