import Lean
import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R01952G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1952_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r1952targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r1952choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1952targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)] c9r1952choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1952targets, c9r1952choice, ?_, checked⟩
    intro S h
    simp only [c9r1952targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 26 _ (by rfl)
  have c9r1953_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r1953targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r1953choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1953targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)] c9r1953choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1953targets, c9r1953choice, ?_, checked⟩
    intro S h
    simp only [c9r1953targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 28 _ (by rfl)
  have c9r1954_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r1954targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r1954choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1954targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)] c9r1954choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1954targets, c9r1954choice, ?_, checked⟩
    intro S h
    simp only [c9r1954targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 30 _ (by rfl)
  have c9r1955_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r1955targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r1955choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1955targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)] c9r1955choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1955targets, c9r1955choice, ?_, checked⟩
    intro S h
    simp only [c9r1955targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 1 _ (by rfl)
  have c9r1956_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r1956targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r1956choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1956targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)] c9r1956choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1956targets, c9r1956choice, ?_, checked⟩
    intro S h
    simp only [c9r1956targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 4 _ (by rfl)
  have c9r1957_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r1957targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r1957choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1957targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)] c9r1957choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1957targets, c9r1957choice, ?_, checked⟩
    intro S h
    simp only [c9r1957targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 7 _ (by rfl)
  have c9r1958_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r1958targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r1958choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1958targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)] c9r1958choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1958targets, c9r1958choice, ?_, checked⟩
    intro S h
    simp only [c9r1958targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 10 _ (by rfl)
  have c9r1959_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r1959targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r1959choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1959targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)] c9r1959choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1959targets, c9r1959choice, ?_, checked⟩
    intro S h
    simp only [c9r1959targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1952_closed
  · subst row; exact c9r1953_closed
  · subst row; exact c9r1954_closed
  · subst row; exact c9r1955_closed
  · subst row; exact c9r1956_closed
  · subst row; exact c9r1957_closed
  · subst row; exact c9r1958_closed
  · subst row; exact c9r1959_closed
theorem C9R01952G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1960_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r1960targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r1960choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1960targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)] c9r1960choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1960targets, c9r1960choice, ?_, checked⟩
    intro S h
    simp only [c9r1960targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 18 _ (by rfl)
  have c9r1961_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r1961targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r1961choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1961targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r1961choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1961targets, c9r1961choice, ?_, checked⟩
    intro S h
    simp only [c9r1961targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 20 _ (by rfl)
  have c9r1962_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r1962targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r1962choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1962targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r1962choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1962targets, c9r1962choice, ?_, checked⟩
    intro S h
    simp only [c9r1962targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 22 _ (by rfl)
  have c9r1963_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r1963targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r1963choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1963targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)] c9r1963choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1963targets, c9r1963choice, ?_, checked⟩
    intro S h
    simp only [c9r1963targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 26 _ (by rfl)
  have c9r1964_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r1964targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r1964choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1964targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)] c9r1964choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1964targets, c9r1964choice, ?_, checked⟩
    intro S h
    simp only [c9r1964targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 29 _ (by rfl)
  have c9r1965_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r1965targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r1965choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1965targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)] c9r1965choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1965targets, c9r1965choice, ?_, checked⟩
    intro S h
    simp only [c9r1965targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 31 _ (by rfl)
  have c9r1966_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r1966targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r1966choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1966targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)] c9r1966choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1966targets, c9r1966choice, ?_, checked⟩
    intro S h
    simp only [c9r1966targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 2 _ (by rfl)
  have c9r1967_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r1967targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r1967choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1967targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)] c9r1967choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1967targets, c9r1967choice, ?_, checked⟩
    intro S h
    simp only [c9r1967targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1960_closed
  · subst row; exact c9r1961_closed
  · subst row; exact c9r1962_closed
  · subst row; exact c9r1963_closed
  · subst row; exact c9r1964_closed
  · subst row; exact c9r1965_closed
  · subst row; exact c9r1966_closed
  · subst row; exact c9r1967_closed
theorem C9R01952G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1968_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r1968targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r1968choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1968targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)] c9r1968choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1968targets, c9r1968choice, ?_, checked⟩
    intro S h
    simp only [c9r1968targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 8 _ (by rfl)
  have c9r1969_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r1969targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,6),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r1969choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,7),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0))),((3,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1969targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)] c9r1969choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1969targets, c9r1969choice, ?_, checked⟩
    intro S h
    simp only [c9r1969targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 14 _ (by rfl)
  have c9r1970_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)] := by
    let c9r1970targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)]]
    let c9r1970choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,6),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((3,5),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1970targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)] c9r1970choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1970targets, c9r1970choice, ?_, checked⟩
    intro S h
    simp only [c9r1970targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 19 _ (by rfl)
  have c9r1971_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)] := by
    let c9r1971targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c9r1971choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,6),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((3,5),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1971targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)] c9r1971choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1971targets, c9r1971choice, ?_, checked⟩
    intro S h
    simp only [c9r1971targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 22 _ (by rfl)
  have c9r1972_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)] := by
    let c9r1972targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c9r1972choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,6),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,5),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1972targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)] c9r1972choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1972targets, c9r1972choice, ?_, checked⟩
    intro S h
    simp only [c9r1972targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 24 _ (by rfl)
  have c9r1973_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r1973targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r1973choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,6),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((3,6),(13,(0,0))),((4,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1973targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)] c9r1973choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1973targets, c9r1973choice, ?_, checked⟩
    intro S h
    simp only [c9r1973targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 26 _ (by rfl)
  have c9r1974_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)] := by
    let c9r1974targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)]]
    let c9r1974choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1974targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)] c9r1974choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1974targets, c9r1974choice, ?_, checked⟩
    intro S h
    simp only [c9r1974targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 31 _ (by rfl)
  have c9r1975_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)] := by
    let c9r1975targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)]]
    let c9r1975choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1975targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)] c9r1975choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1975targets, c9r1975choice, ?_, checked⟩
    intro S h
    simp only [c9r1975targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1968_closed
  · subst row; exact c9r1969_closed
  · subst row; exact c9r1970_closed
  · subst row; exact c9r1971_closed
  · subst row; exact c9r1972_closed
  · subst row; exact c9r1973_closed
  · subst row; exact c9r1974_closed
  · subst row; exact c9r1975_closed
theorem C9R01952G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1976_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)] := by
    let c9r1976targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)]]
    let c9r1976choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((3,5),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1976targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)] c9r1976choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1976targets, c9r1976choice, ?_, checked⟩
    intro S h
    simp only [c9r1976targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 5 _ (by rfl)
  have c9r1977_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)] := by
    let c9r1977targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)]]
    let c9r1977choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1977targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)] c9r1977choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1977targets, c9r1977choice, ?_, checked⟩
    intro S h
    simp only [c9r1977targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 8 _ (by rfl)
  have c9r1978_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)] := by
    let c9r1978targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]]
    let c9r1978choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,5),(10,(0,0))),((4,3),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1978targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)] c9r1978choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1978targets, c9r1978choice, ?_, checked⟩
    intro S h
    simp only [c9r1978targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 11 _ (by rfl)
  have c9r1979_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)] := by
    let c9r1979targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)]]
    let c9r1979choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1979targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)] c9r1979choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1979targets, c9r1979choice, ?_, checked⟩
    intro S h
    simp only [c9r1979targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 14 _ (by rfl)
  have c9r1980_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)] := by
    let c9r1980targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)]]
    let c9r1980choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((3,6),(11,(0,0))),((4,4),(12,(0,0))),((4,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1980targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)] c9r1980choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1980targets, c9r1980choice, ?_, checked⟩
    intro S h
    simp only [c9r1980targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 17 _ (by rfl)
  have c9r1981_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)] := by
    let c9r1981targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)]]
    let c9r1981choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((3,5),(11,(0,0))),((4,3),(12,(0,0))),((4,5),(13,(0,0))),((5,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1981targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)] c9r1981choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1981targets, c9r1981choice, ?_, checked⟩
    intro S h
    simp only [c9r1981targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 20 _ (by rfl)
  have c9r1982_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r1982targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r1982choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1982targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r1982choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1982targets, c9r1982choice, ?_, checked⟩
    intro S h
    simp only [c9r1982targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 25 _ (by rfl)
  have c9r1983_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r1983targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1983choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1983targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)] c9r1983choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1983targets, c9r1983choice, ?_, checked⟩
    intro S h
    simp only [c9r1983targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1976_closed
  · subst row; exact c9r1977_closed
  · subst row; exact c9r1978_closed
  · subst row; exact c9r1979_closed
  · subst row; exact c9r1980_closed
  · subst row; exact c9r1981_closed
  · subst row; exact c9r1982_closed
  · subst row; exact c9r1983_closed
theorem C9R01952_closed (row : List GridPoint) (h : FamilyMember row F9B000L61) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L61, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R01952G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01952G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01952G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01952G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01952G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01952G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01952G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01952G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01952G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01952G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01952G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01952G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01952G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01952G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01952G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01952G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01952G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01952G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01952G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01952G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01952G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01952G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01952G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01952G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01952G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01952G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01952G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01952G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01952G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01952G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01952G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01952G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
