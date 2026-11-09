import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R02656G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2656_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c9r2656targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,0),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,6),(1,0),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,6),(0,7),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c9r2656choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((-1,6),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,3),(6,(0,0))),((0,4),(7,(0,0))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,6),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,2),(13,(0,0))),((2,3),(14,(0,0))),((2,4),(15,(0,0))),((2,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2656targets [(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c9r2656choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2656targets, c9r2656choice, ?_, checked⟩
    intro S h
    simp only [c9r2656targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 1 _ (by rfl)
  have c9r2657_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c9r2657targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c9r2657choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0))),((2,5),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2657targets [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c9r2657choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2657targets, c9r2657choice, ?_, checked⟩
    intro S h
    simp only [c9r2657targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 9 _ (by rfl)
  have c9r2658_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] := by
    let c9r2658targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)]]
    let c9r2658choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,6),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0))),((2,5),(15,(0,0))),((3,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2658targets [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] c9r2658choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2658targets, c9r2658choice, ?_, checked⟩
    intro S h
    simp only [c9r2658targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 15 _ (by rfl)
  have c9r2659_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] := by
    let c9r2659targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)]]
    let c9r2659choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((3,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2659targets [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] c9r2659choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2659targets, c9r2659choice, ?_, checked⟩
    intro S h
    simp only [c9r2659targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 20 _ (by rfl)
  have c9r2660_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] := by
    let c9r2660targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)]]
    let c9r2660choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((3,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2660targets [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] c9r2660choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2660targets, c9r2660choice, ?_, checked⟩
    intro S h
    simp only [c9r2660targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 24 _ (by rfl)
  have c9r2661_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] := by
    let c9r2661targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)]]
    let c9r2661choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2661targets [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] c9r2661choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2661targets, c9r2661choice, ?_, checked⟩
    intro S h
    simp only [c9r2661targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 27 _ (by rfl)
  have c9r2662_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] := by
    let c9r2662targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)]]
    let c9r2662choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,5),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2662targets [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] c9r2662choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2662targets, c9r2662choice, ?_, checked⟩
    intro S h
    simp only [c9r2662targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 29 _ (by rfl)
  have c9r2663_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] := by
    let c9r2663targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,5),(1,0),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,6),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)]]
    let c9r2663choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,5),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0))),((2,6),(15,(0,0))),((3,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2663targets [(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] c9r2663choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2663targets, c9r2663choice, ?_, checked⟩
    intro S h
    simp only [c9r2663targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2656_closed
  · subst row; exact c9r2657_closed
  · subst row; exact c9r2658_closed
  · subst row; exact c9r2659_closed
  · subst row; exact c9r2660_closed
  · subst row; exact c9r2661_closed
  · subst row; exact c9r2662_closed
  · subst row; exact c9r2663_closed
theorem C9R02656G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2664_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c9r2664targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,6),(1,0),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,7),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,4),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c9r2664choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,6),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,5),(7,(0,0))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,7),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,2),(13,(0,0))),((2,3),(14,(0,0))),((2,4),(15,(0,0))),((2,5),(16,(0,0))),((2,6),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2664targets [(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c9r2664choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2664targets, c9r2664choice, ?_, checked⟩
    intro S h
    simp only [c9r2664targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 18 _ (by rfl)
  have c9r2665_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)] := by
    let c9r2665targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)]]
    let c9r2665choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,8),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,2),(13,(0,0))),((2,3),(14,(0,0))),((2,4),(15,(0,0))),((2,5),(16,(0,0))),((2,6),(17,(0,0))),((2,7),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2665targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)] c9r2665choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2665targets, c9r2665choice, ?_, checked⟩
    intro S h
    simp only [c9r2665targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 28 _ (by rfl)
  have c9r2666_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)] := by
    let c9r2666targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)]]
    let c9r2666choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0))),((2,5),(15,(0,0))),((2,6),(16,(0,0))),((3,0),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2666targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)] c9r2666choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2666targets, c9r2666choice, ?_, checked⟩
    intro S h
    simp only [c9r2666targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 3 _ (by rfl)
  have c9r2667_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)] := by
    let c9r2667targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)]]
    let c9r2667choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0))),((3,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2667targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)] c9r2667choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2667targets, c9r2667choice, ?_, checked⟩
    intro S h
    simp only [c9r2667targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 9 _ (by rfl)
  have c9r2668_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)] := by
    let c9r2668targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)]]
    let c9r2668choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0))),((3,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2668targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)] c9r2668choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2668targets, c9r2668choice, ?_, checked⟩
    intro S h
    simp only [c9r2668targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 14 _ (by rfl)
  have c9r2669_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)] := by
    let c9r2669targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)]]
    let c9r2669choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0))),((3,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2669targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)] c9r2669choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2669targets, c9r2669choice, ?_, checked⟩
    intro S h
    simp only [c9r2669targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 18 _ (by rfl)
  have c9r2670_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)] := by
    let c9r2670targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)]]
    let c9r2670choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0))),((3,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2670targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)] c9r2670choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2670targets, c9r2670choice, ?_, checked⟩
    intro S h
    simp only [c9r2670targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 21 _ (by rfl)
  have c9r2671_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)] := by
    let c9r2671targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)]]
    let c9r2671choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0))),((2,6),(15,(0,0))),((3,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2671targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)] c9r2671choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2671targets, c9r2671choice, ?_, checked⟩
    intro S h
    simp only [c9r2671targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2664_closed
  · subst row; exact c9r2665_closed
  · subst row; exact c9r2666_closed
  · subst row; exact c9r2667_closed
  · subst row; exact c9r2668_closed
  · subst row; exact c9r2669_closed
  · subst row; exact c9r2670_closed
  · subst row; exact c9r2671_closed
theorem C9R02656G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2672_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)] := by
    let c9r2672targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)]]
    let c9r2672choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,7),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0))),((2,5),(15,(0,0))),((2,7),(16,(0,0))),((3,6),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2672targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)] c9r2672choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2672targets, c9r2672choice, ?_, checked⟩
    intro S h
    simp only [c9r2672targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 25 _ (by rfl)
  have c9r2673_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] := by
    let c9r2673targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)]]
    let c9r2673choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,0),(14,(0,0))),((3,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2673targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] c9r2673choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2673targets, c9r2673choice, ?_, checked⟩
    intro S h
    simp only [c9r2673targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 31 _ (by rfl)
  have c9r2674_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)] := by
    let c9r2674targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)]]
    let c9r2674choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,0),(14,(0,0))),((3,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2674targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)] c9r2674choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2674targets, c9r2674choice, ?_, checked⟩
    intro S h
    simp only [c9r2674targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 4 _ (by rfl)
  have c9r2675_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)] := by
    let c9r2675targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)]]
    let c9r2675choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,0),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2675targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)] c9r2675choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2675targets, c9r2675choice, ?_, checked⟩
    intro S h
    simp only [c9r2675targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 8 _ (by rfl)
  have c9r2676_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)] := by
    let c9r2676targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)]]
    let c9r2676choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,0),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2676targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)] c9r2676choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2676targets, c9r2676choice, ?_, checked⟩
    intro S h
    simp only [c9r2676targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 11 _ (by rfl)
  have c9r2677_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)] := by
    let c9r2677targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)]]
    let c9r2677choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,6),(14,(0,0))),((3,0),(15,(0,0))),((3,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2677targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)] c9r2677choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2677targets, c9r2677choice, ?_, checked⟩
    intro S h
    simp only [c9r2677targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 14 _ (by rfl)
  have c9r2678_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)] := by
    let c9r2678targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)]]
    let c9r2678choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((3,-1),(15,(0,1))),((3,1),(16,(0,0))),((4,0),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2678targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)] c9r2678choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2678targets, c9r2678choice, ?_, checked⟩
    intro S h
    simp only [c9r2678targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 16 _ (by rfl)
  have c9r2679_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)] := by
    let c9r2679targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)]]
    let c9r2679choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((2,5),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2679targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)] c9r2679choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2679targets, c9r2679choice, ?_, checked⟩
    intro S h
    simp only [c9r2679targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2672_closed
  · subst row; exact c9r2673_closed
  · subst row; exact c9r2674_closed
  · subst row; exact c9r2675_closed
  · subst row; exact c9r2676_closed
  · subst row; exact c9r2677_closed
  · subst row; exact c9r2678_closed
  · subst row; exact c9r2679_closed
theorem C9R02656G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2680_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)] := by
    let c9r2680targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,3)]]
    let c9r2680choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((2,5),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2680targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)] c9r2680choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2680targets, c9r2680choice, ?_, checked⟩
    intro S h
    simp only [c9r2680targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 25 _ (by rfl)
  have c9r2681_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)] := by
    let c9r2681targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,4)]]
    let c9r2681choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,1),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2681targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)] c9r2681choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2681targets, c9r2681choice, ?_, checked⟩
    intro S h
    simp only [c9r2681targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 28 _ (by rfl)
  have c9r2682_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)] := by
    let c9r2682targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,5)]]
    let c9r2682choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,1),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2682targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)] c9r2682choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2682targets, c9r2682choice, ?_, checked⟩
    intro S h
    simp only [c9r2682targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 31 _ (by rfl)
  have c9r2683_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)] := by
    let c9r2683targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1),(4,1)]]
    let c9r2683choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,0),(14,(0,0))),((3,2),(15,(0,0))),((4,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2683targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)] c9r2683choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2683targets, c9r2683choice, ?_, checked⟩
    intro S h
    simp only [c9r2683targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 2 _ (by rfl)
  have c9r2684_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)] := by
    let c9r2684targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,3)]]
    let c9r2684choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,4),(11,(0,0))),((2,5),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2684targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)] c9r2684choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2684targets, c9r2684choice, ?_, checked⟩
    intro S h
    simp only [c9r2684targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 6 _ (by rfl)
  have c9r2685_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)] := by
    let c9r2685targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,4)]]
    let c9r2685choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2685targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)] c9r2685choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2685targets, c9r2685choice, ?_, checked⟩
    intro S h
    simp only [c9r2685targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 9 _ (by rfl)
  have c9r2686_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)] := by
    let c9r2686targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,5)]]
    let c9r2686choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,2),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2686targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)] c9r2686choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2686targets, c9r2686choice, ?_, checked⟩
    intro S h
    simp only [c9r2686targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 12 _ (by rfl)
  have c9r2687_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)] := by
    let c9r2687targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2),(4,2)]]
    let c9r2687choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,1),(14,(0,0))),((3,3),(15,(0,0))),((4,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2687targets [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)] c9r2687choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2687targets, c9r2687choice, ?_, checked⟩
    intro S h
    simp only [c9r2687targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2680_closed
  · subst row; exact c9r2681_closed
  · subst row; exact c9r2682_closed
  · subst row; exact c9r2683_closed
  · subst row; exact c9r2684_closed
  · subst row; exact c9r2685_closed
  · subst row; exact c9r2686_closed
  · subst row; exact c9r2687_closed
theorem C9R02656_closed (row : List GridPoint) (h : FamilyMember row F9B001L19) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L19, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R02656G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02656G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02656G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02656G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02656G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02656G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02656G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02656G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02656G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02656G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02656G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02656G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02656G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02656G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02656G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02656G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02656G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02656G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02656G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02656G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02656G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02656G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02656G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02656G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02656G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02656G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02656G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02656G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02656G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02656G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02656G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02656G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
