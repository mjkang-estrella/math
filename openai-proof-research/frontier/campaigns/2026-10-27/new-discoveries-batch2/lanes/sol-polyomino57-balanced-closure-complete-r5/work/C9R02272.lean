import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R02272G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2272_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)] := by
    let c9r2272targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)]]
    let c9r2272choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2272targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)] c9r2272choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2272targets, c9r2272choice, ?_, checked⟩
    intro S h
    simp only [c9r2272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 3 _ (by rfl)
  have c9r2273_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)] := by
    let c9r2273targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)]]
    let c9r2273choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2273targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)] c9r2273choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2273targets, c9r2273choice, ?_, checked⟩
    intro S h
    simp only [c9r2273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 6 _ (by rfl)
  have c9r2274_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)] := by
    let c9r2274targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)]]
    let c9r2274choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,5),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0))),((5,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2274targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)] c9r2274choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2274targets, c9r2274choice, ?_, checked⟩
    intro S h
    simp only [c9r2274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 10 _ (by rfl)
  have c9r2275_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)] := by
    let c9r2275targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)]]
    let c9r2275choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2275targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)] c9r2275choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2275targets, c9r2275choice, ?_, checked⟩
    intro S h
    simp only [c9r2275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 13 _ (by rfl)
  have c9r2276_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)] := by
    let c9r2276targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(6,3)]]
    let c9r2276choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,4),(13,(0,0))),((6,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2276targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)] c9r2276choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2276targets, c9r2276choice, ?_, checked⟩
    intro S h
    simp only [c9r2276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 15 _ (by rfl)
  have c9r2277_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)] := by
    let c9r2277targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)]]
    let c9r2277choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2277targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)] c9r2277choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2277targets, c9r2277choice, ?_, checked⟩
    intro S h
    simp only [c9r2277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 19 _ (by rfl)
  have c9r2278_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)] := by
    let c9r2278targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,3)]]
    let c9r2278choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,4),(13,(0,0))),((6,2),(14,(0,0))),((6,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2278targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)] c9r2278choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2278targets, c9r2278choice, ?_, checked⟩
    intro S h
    simp only [c9r2278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 22 _ (by rfl)
  have c9r2279_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)] := by
    let c9r2279targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2),(7,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2),(7,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2),(7,2)]]
    let c9r2279choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,3),(15,(0,0))),((7,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2279targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)] c9r2279choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2279targets, c9r2279choice, ?_, checked⟩
    intro S h
    simp only [c9r2279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 25 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2272_closed
  · subst row; exact c9r2273_closed
  · subst row; exact c9r2274_closed
  · subst row; exact c9r2275_closed
  · subst row; exact c9r2276_closed
  · subst row; exact c9r2277_closed
  · subst row; exact c9r2278_closed
  · subst row; exact c9r2279_closed
theorem C9R02272G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2280_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)] := by
    let c9r2280targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,3),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,3),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)]]
    let c9r2280choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,4),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0))),((5,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2280targets [(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)] c9r2280choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2280targets, c9r2280choice, ?_, checked⟩
    intro S h
    simp only [c9r2280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 31 _ (by rfl)
  have c9r2281_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r2281targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r2281choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,4),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0))),((5,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2281targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)] c9r2281choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2281targets, c9r2281choice, ?_, checked⟩
    intro S h
    simp only [c9r2281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 5 _ (by rfl)
  have c9r2282_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r2282targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r2282choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((6,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2282targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)] c9r2282choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2282targets, c9r2282choice, ?_, checked⟩
    intro S h
    simp only [c9r2282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 8 _ (by rfl)
  have c9r2283_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r2283targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r2283choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2283targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)] c9r2283choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2283targets, c9r2283choice, ?_, checked⟩
    intro S h
    simp only [c9r2283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 10 _ (by rfl)
  have c9r2284_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r2284targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r2284choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2284targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)] c9r2284choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2284targets, c9r2284choice, ?_, checked⟩
    intro S h
    simp only [c9r2284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 12 _ (by rfl)
  have c9r2285_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)] := by
    let c9r2285targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)]]
    let c9r2285choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2285targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)] c9r2285choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2285targets, c9r2285choice, ?_, checked⟩
    intro S h
    simp only [c9r2285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 15 _ (by rfl)
  have c9r2286_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)] := by
    let c9r2286targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)]]
    let c9r2286choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,-1),(14,(0,1))),((6,1),(15,(0,0))),((7,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2286targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)] c9r2286choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2286targets, c9r2286choice, ?_, checked⟩
    intro S h
    simp only [c9r2286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 17 _ (by rfl)
  have c9r2287_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)] := by
    let c9r2287targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)]]
    let c9r2287choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2287targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)] c9r2287choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2287targets, c9r2287choice, ?_, checked⟩
    intro S h
    simp only [c9r2287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2280_closed
  · subst row; exact c9r2281_closed
  · subst row; exact c9r2282_closed
  · subst row; exact c9r2283_closed
  · subst row; exact c9r2284_closed
  · subst row; exact c9r2285_closed
  · subst row; exact c9r2286_closed
  · subst row; exact c9r2287_closed
theorem C9R02272G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2288_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)] := by
    let c9r2288targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c9r2288choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2288targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)] c9r2288choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2288targets, c9r2288choice, ?_, checked⟩
    intro S h
    simp only [c9r2288targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 23 _ (by rfl)
  have c9r2289_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)] := by
    let c9r2289targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,4),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,4)]]
    let c9r2289choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,5),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0))),((5,3),(16,(0,0))),((5,4),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2289targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)] c9r2289choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2289targets, c9r2289choice, ?_, checked⟩
    intro S h
    simp only [c9r2289targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 28 _ (by rfl)
  have c9r2290_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)] := by
    let c9r2290targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(6,1)]]
    let c9r2290choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,0),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0))),((6,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2290targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)] c9r2290choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2290targets, c9r2290choice, ?_, checked⟩
    intro S h
    simp only [c9r2290targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 0 _ (by rfl)
  have c9r2291_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)] := by
    let c9r2291targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(6,2)]]
    let c9r2291choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,3),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2291targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)] c9r2291choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2291targets, c9r2291choice, ?_, checked⟩
    intro S h
    simp only [c9r2291targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 2 _ (by rfl)
  have c9r2292_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)] := by
    let c9r2292targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3),(6,3)]]
    let c9r2292choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,4),(15,(0,0))),((6,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2292targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)] c9r2292choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2292targets, c9r2292choice, ?_, checked⟩
    intro S h
    simp only [c9r2292targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 4 _ (by rfl)
  have c9r2293_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r2293targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r2293choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2293targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)] c9r2293choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2293targets, c9r2293choice, ?_, checked⟩
    intro S h
    simp only [c9r2293targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 7 _ (by rfl)
  have c9r2294_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)] := by
    let c9r2294targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)]]
    let c9r2294choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2294targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)] c9r2294choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2294targets, c9r2294choice, ?_, checked⟩
    intro S h
    simp only [c9r2294targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 10 _ (by rfl)
  have c9r2295_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)] := by
    let c9r2295targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)]]
    let c9r2295choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2295targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)] c9r2295choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2295targets, c9r2295choice, ?_, checked⟩
    intro S h
    simp only [c9r2295targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2288_closed
  · subst row; exact c9r2289_closed
  · subst row; exact c9r2290_closed
  · subst row; exact c9r2291_closed
  · subst row; exact c9r2292_closed
  · subst row; exact c9r2293_closed
  · subst row; exact c9r2294_closed
  · subst row; exact c9r2295_closed
theorem C9R02272G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2296_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)] := by
    let c9r2296targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,3)]]
    let c9r2296choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,4),(13,(0,0))),((6,2),(14,(0,0))),((6,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2296targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)] c9r2296choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2296targets, c9r2296choice, ?_, checked⟩
    intro S h
    simp only [c9r2296targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 16 _ (by rfl)
  have c9r2297_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)] := by
    let c9r2297targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2),(7,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2),(7,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2),(7,2)]]
    let c9r2297choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,3),(15,(0,0))),((7,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2297targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)] c9r2297choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2297targets, c9r2297choice, ?_, checked⟩
    intro S h
    simp only [c9r2297targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 19 _ (by rfl)
  have c9r2298_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)] := by
    let c9r2298targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c9r2298choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,3),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0))),((6,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2298targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)] c9r2298choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2298targets, c9r2298choice, ?_, checked⟩
    intro S h
    simp only [c9r2298targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 24 _ (by rfl)
  have c9r2299_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)] := by
    let c9r2299targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c9r2299choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,-1),(14,(0,1))),((6,1),(15,(0,0))),((7,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2299targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)] c9r2299choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2299targets, c9r2299choice, ?_, checked⟩
    intro S h
    simp only [c9r2299targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 26 _ (by rfl)
  have c9r2300_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)] := by
    let c9r2300targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c9r2300choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2300targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)] c9r2300choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2300targets, c9r2300choice, ?_, checked⟩
    intro S h
    simp only [c9r2300targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 28 _ (by rfl)
  have c9r2301_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)] := by
    let c9r2301targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,3),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,3)]]
    let c9r2301choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((5,0),(13,(0,0))),((5,4),(14,(0,0))),((6,1),(15,(0,0))),((6,2),(16,(0,0))),((6,3),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2301targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)] c9r2301choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2301targets, c9r2301choice, ?_, checked⟩
    intro S h
    simp only [c9r2301targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,true] 0 _ (by rfl)
  have c9r2302_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)] := by
    let c9r2302targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)]]
    let c9r2302choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2302targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)] c9r2302choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2302targets, c9r2302choice, ?_, checked⟩
    intro S h
    simp only [c9r2302targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,true] 3 _ (by rfl)
  have c9r2303_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)] := by
    let c9r2303targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2),(7,2)]]
    let c9r2303choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,3),(15,(0,0))),((7,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2303targets [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)] c9r2303choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2303targets, c9r2303choice, ?_, checked⟩
    intro S h
    simp only [c9r2303targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,true,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2296_closed
  · subst row; exact c9r2297_closed
  · subst row; exact c9r2298_closed
  · subst row; exact c9r2299_closed
  · subst row; exact c9r2300_closed
  · subst row; exact c9r2301_closed
  · subst row; exact c9r2302_closed
  · subst row; exact c9r2303_closed
theorem C9R02272_closed (row : List GridPoint) (h : FamilyMember row F9B001L7) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L7, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R02272G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02272G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02272G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02272G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02272G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02272G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02272G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02272G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02272G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02272G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02272G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02272G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02272G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02272G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02272G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02272G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02272G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02272G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02272G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02272G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02272G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02272G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02272G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02272G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02272G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02272G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02272G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02272G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02272G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02272G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02272G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02272G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
