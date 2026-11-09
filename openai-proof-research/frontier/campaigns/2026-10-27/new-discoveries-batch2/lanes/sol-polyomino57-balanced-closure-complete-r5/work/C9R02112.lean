import Lean
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R02112G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2112_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)] := by
    let c9r2112targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1),(6,1)]]
    let c9r2112choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2112targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)] c9r2112choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2112targets, c9r2112choice, ?_, checked⟩
    intro S h
    simp only [c9r2112targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 27 _ (by rfl)
  have c9r2113_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)] := by
    let c9r2113targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,1)]]
    let c9r2113choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2113targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)] c9r2113choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2113targets, c9r2113choice, ?_, checked⟩
    intro S h
    simp only [c9r2113targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 30 _ (by rfl)
  have c9r2114_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)] := by
    let c9r2114targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0),(7,0)]]
    let c9r2114choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,-1),(14,(0,1))),((6,1),(15,(0,0))),((7,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2114targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)] c9r2114choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2114targets, c9r2114choice, ?_, checked⟩
    intro S h
    simp only [c9r2114targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 0 _ (by rfl)
  have c9r2115_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r2115targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r2115choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,5),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2115targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)] c9r2115choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2115targets, c9r2115choice, ?_, checked⟩
    intro S h
    simp only [c9r2115targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 5 _ (by rfl)
  have c9r2116_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r2116targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r2116choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2116targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)] c9r2116choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2116targets, c9r2116choice, ?_, checked⟩
    intro S h
    simp only [c9r2116targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 9 _ (by rfl)
  have c9r2117_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r2117targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r2117choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2117targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)] c9r2117choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2117targets, c9r2117choice, ?_, checked⟩
    intro S h
    simp only [c9r2117targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 11 _ (by rfl)
  have c9r2118_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r2118targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r2118choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2118targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)] c9r2118choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2118targets, c9r2118choice, ?_, checked⟩
    intro S h
    simp only [c9r2118targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 13 _ (by rfl)
  have c9r2119_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r2119targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r2119choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2119targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)] c9r2119choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2119targets, c9r2119choice, ?_, checked⟩
    intro S h
    simp only [c9r2119targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2112_closed
  · subst row; exact c9r2113_closed
  · subst row; exact c9r2114_closed
  · subst row; exact c9r2115_closed
  · subst row; exact c9r2116_closed
  · subst row; exact c9r2117_closed
  · subst row; exact c9r2118_closed
  · subst row; exact c9r2119_closed
theorem C9R02112G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2120_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r2120targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r2120choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2120targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)] c9r2120choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2120targets, c9r2120choice, ?_, checked⟩
    intro S h
    simp only [c9r2120targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 19 _ (by rfl)
  have c9r2121_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r2121targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r2121choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2121targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)] c9r2121choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2121targets, c9r2121choice, ?_, checked⟩
    intro S h
    simp only [c9r2121targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 22 _ (by rfl)
  have c9r2122_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r2122targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r2122choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2122targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)] c9r2122choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2122targets, c9r2122choice, ?_, checked⟩
    intro S h
    simp only [c9r2122targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 25 _ (by rfl)
  have c9r2123_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r2123targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r2123choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2123targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)] c9r2123choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2123targets, c9r2123choice, ?_, checked⟩
    intro S h
    simp only [c9r2123targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 28 _ (by rfl)
  have c9r2124_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r2124targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r2124choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2124targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)] c9r2124choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2124targets, c9r2124choice, ?_, checked⟩
    intro S h
    simp only [c9r2124targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 1 _ (by rfl)
  have c9r2125_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r2125targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r2125choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2125targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r2125choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2125targets, c9r2125choice, ?_, checked⟩
    intro S h
    simp only [c9r2125targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 3 _ (by rfl)
  have c9r2126_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r2126targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r2126choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2126targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r2126choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2126targets, c9r2126choice, ?_, checked⟩
    intro S h
    simp only [c9r2126targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 5 _ (by rfl)
  have c9r2127_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r2127targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r2127choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2127targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)] c9r2127choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2127targets, c9r2127choice, ?_, checked⟩
    intro S h
    simp only [c9r2127targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2120_closed
  · subst row; exact c9r2121_closed
  · subst row; exact c9r2122_closed
  · subst row; exact c9r2123_closed
  · subst row; exact c9r2124_closed
  · subst row; exact c9r2125_closed
  · subst row; exact c9r2126_closed
  · subst row; exact c9r2127_closed
theorem C9R02112G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2128_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r2128targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r2128choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2128targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)] c9r2128choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2128targets, c9r2128choice, ?_, checked⟩
    intro S h
    simp only [c9r2128targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 12 _ (by rfl)
  have c9r2129_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r2129targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r2129choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2129targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)] c9r2129choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2129targets, c9r2129choice, ?_, checked⟩
    intro S h
    simp only [c9r2129targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 14 _ (by rfl)
  have c9r2130_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r2130targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r2130choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2130targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)] c9r2130choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2130targets, c9r2130choice, ?_, checked⟩
    intro S h
    simp only [c9r2130targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 17 _ (by rfl)
  have c9r2131_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r2131targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r2131choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2131targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)] c9r2131choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2131targets, c9r2131choice, ?_, checked⟩
    intro S h
    simp only [c9r2131targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 20 _ (by rfl)
  have c9r2132_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r2132targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r2132choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2132targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] c9r2132choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2132targets, c9r2132choice, ?_, checked⟩
    intro S h
    simp only [c9r2132targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 23 _ (by rfl)
  have c9r2133_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r2133targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,6),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r2133choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,7),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0))),((3,5),(16,(0,0))),((3,6),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2133targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] c9r2133choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2133targets, c9r2133choice, ?_, checked⟩
    intro S h
    simp only [c9r2133targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 30 _ (by rfl)
  have c9r2134_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)] := by
    let c9r2134targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)]]
    let c9r2134choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,6),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((3,5),(15,(0,0))),((4,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2134targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)] c9r2134choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2134targets, c9r2134choice, ?_, checked⟩
    intro S h
    simp only [c9r2134targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 4 _ (by rfl)
  have c9r2135_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)] := by
    let c9r2135targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)]]
    let c9r2135choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,6),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2135targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)] c9r2135choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2135targets, c9r2135choice, ?_, checked⟩
    intro S h
    simp only [c9r2135targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 8 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2128_closed
  · subst row; exact c9r2129_closed
  · subst row; exact c9r2130_closed
  · subst row; exact c9r2131_closed
  · subst row; exact c9r2132_closed
  · subst row; exact c9r2133_closed
  · subst row; exact c9r2134_closed
  · subst row; exact c9r2135_closed
theorem C9R02112G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2136_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)] := by
    let c9r2136targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c9r2136choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,6),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2136targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)] c9r2136choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2136targets, c9r2136choice, ?_, checked⟩
    intro S h
    simp only [c9r2136targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 11 _ (by rfl)
  have c9r2137_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)] := by
    let c9r2137targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c9r2137choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,6),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,5),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2137targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)] c9r2137choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2137targets, c9r2137choice, ?_, checked⟩
    intro S h
    simp only [c9r2137targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 13 _ (by rfl)
  have c9r2138_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r2138targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r2138choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,6),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((3,6),(15,(0,0))),((4,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2138targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)] c9r2138choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2138targets, c9r2138choice, ?_, checked⟩
    intro S h
    simp only [c9r2138targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 15 _ (by rfl)
  have c9r2139_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] := by
    let c9r2139targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)]]
    let c9r2139choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((4,0),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2139targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] c9r2139choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2139targets, c9r2139choice, ?_, checked⟩
    intro S h
    simp only [c9r2139targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 20 _ (by rfl)
  have c9r2140_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)] := by
    let c9r2140targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)]]
    let c9r2140choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2140targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)] c9r2140choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2140targets, c9r2140choice, ?_, checked⟩
    intro S h
    simp only [c9r2140targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 24 _ (by rfl)
  have c9r2141_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)] := by
    let c9r2141targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,3)]]
    let c9r2141choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2141targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)] c9r2141choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2141targets, c9r2141choice, ?_, checked⟩
    intro S h
    simp only [c9r2141targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 27 _ (by rfl)
  have c9r2142_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)] := by
    let c9r2142targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,4)]]
    let c9r2142choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,5),(13,(0,0))),((4,1),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2142targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)] c9r2142choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2142targets, c9r2142choice, ?_, checked⟩
    intro S h
    simp only [c9r2142targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 30 _ (by rfl)
  have c9r2143_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)] := by
    let c9r2143targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1),(5,1)]]
    let c9r2143choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((4,0),(14,(0,0))),((4,2),(15,(0,0))),((5,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2143targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)] c9r2143choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2143targets, c9r2143choice, ?_, checked⟩
    intro S h
    simp only [c9r2143targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2136_closed
  · subst row; exact c9r2137_closed
  · subst row; exact c9r2138_closed
  · subst row; exact c9r2139_closed
  · subst row; exact c9r2140_closed
  · subst row; exact c9r2141_closed
  · subst row; exact c9r2142_closed
  · subst row; exact c9r2143_closed
theorem C9R02112_closed (row : List GridPoint) (h : FamilyMember row F9B001L2) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L2, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R02112G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02112G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02112G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02112G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02112G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02112G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02112G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02112G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02112G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02112G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02112G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02112G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02112G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02112G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02112G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02112G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02112G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02112G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02112G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02112G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02112G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02112G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02112G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02112G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02112G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02112G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02112G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02112G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02112G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02112G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02112G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02112G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
