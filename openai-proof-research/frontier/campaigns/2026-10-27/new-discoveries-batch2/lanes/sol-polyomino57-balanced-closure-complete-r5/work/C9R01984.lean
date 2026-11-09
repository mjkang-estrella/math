import Lean
import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R01984G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1984_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)] := by
    let c9r1984targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)]]
    let c9r1984choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1984targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)] c9r1984choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1984targets, c9r1984choice, ?_, checked⟩
    intro S h
    simp only [c9r1984targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 0 _ (by rfl)
  have c9r1985_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)] := by
    let c9r1985targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)]]
    let c9r1985choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1985targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)] c9r1985choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1985targets, c9r1985choice, ?_, checked⟩
    intro S h
    simp only [c9r1985targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 2 _ (by rfl)
  have c9r1986_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)] := by
    let c9r1986targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)]]
    let c9r1986choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,5),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1986targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)] c9r1986choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1986targets, c9r1986choice, ?_, checked⟩
    intro S h
    simp only [c9r1986targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 6 _ (by rfl)
  have c9r1987_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)] := by
    let c9r1987targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)]]
    let c9r1987choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1987targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)] c9r1987choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1987targets, c9r1987choice, ?_, checked⟩
    intro S h
    simp only [c9r1987targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 9 _ (by rfl)
  have c9r1988_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)] := by
    let c9r1988targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)]]
    let c9r1988choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,4),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1988targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)] c9r1988choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1988targets, c9r1988choice, ?_, checked⟩
    intro S h
    simp only [c9r1988targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 11 _ (by rfl)
  have c9r1989_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)] := by
    let c9r1989targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)]]
    let c9r1989choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1989targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)] c9r1989choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1989targets, c9r1989choice, ?_, checked⟩
    intro S h
    simp only [c9r1989targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 15 _ (by rfl)
  have c9r1990_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)] := by
    let c9r1990targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)]]
    let c9r1990choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1990targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)] c9r1990choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1990targets, c9r1990choice, ?_, checked⟩
    intro S h
    simp only [c9r1990targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 18 _ (by rfl)
  have c9r1991_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)] := by
    let c9r1991targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)]]
    let c9r1991choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1991targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)] c9r1991choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1991targets, c9r1991choice, ?_, checked⟩
    intro S h
    simp only [c9r1991targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 21 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1984_closed
  · subst row; exact c9r1985_closed
  · subst row; exact c9r1986_closed
  · subst row; exact c9r1987_closed
  · subst row; exact c9r1988_closed
  · subst row; exact c9r1989_closed
  · subst row; exact c9r1990_closed
  · subst row; exact c9r1991_closed
theorem C9R01984G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1992_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)] := by
    let c9r1992targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)]]
    let c9r1992choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,6),(10,(0,0))),((4,3),(11,(0,0))),((4,4),(12,(0,0))),((4,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1992targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)] c9r1992choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1992targets, c9r1992choice, ?_, checked⟩
    intro S h
    simp only [c9r1992targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 25 _ (by rfl)
  have c9r1993_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)] := by
    let c9r1993targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)]]
    let c9r1993choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,5),(9,(0,0))),((4,2),(10,(0,0))),((4,4),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1993targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)] c9r1993choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1993targets, c9r1993choice, ?_, checked⟩
    intro S h
    simp only [c9r1993targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 28 _ (by rfl)
  have c9r1994_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)] := by
    let c9r1994targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)]]
    let c9r1994choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,5),(9,(0,0))),((4,3),(10,(0,0))),((4,5),(11,(0,0))),((5,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1994targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)] c9r1994choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1994targets, c9r1994choice, ?_, checked⟩
    intro S h
    simp only [c9r1994targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 30 _ (by rfl)
  have c9r1995_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)] := by
    let c9r1995targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)]]
    let c9r1995choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1995targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)] c9r1995choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1995targets, c9r1995choice, ?_, checked⟩
    intro S h
    simp only [c9r1995targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 2 _ (by rfl)
  have c9r1996_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)] := by
    let c9r1996targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)]]
    let c9r1996choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,5),(11,(0,0))),((5,3),(12,(0,0))),((5,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1996targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)] c9r1996choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1996targets, c9r1996choice, ?_, checked⟩
    intro S h
    simp only [c9r1996targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 5 _ (by rfl)
  have c9r1997_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)] := by
    let c9r1997targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)]]
    let c9r1997choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,4),(13,(0,0))),((6,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1997targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)] c9r1997choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1997targets, c9r1997choice, ?_, checked⟩
    intro S h
    simp only [c9r1997targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 8 _ (by rfl)
  have c9r1998_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)] := by
    let c9r1998targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)]]
    let c9r1998choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,5),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1998targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)] c9r1998choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1998targets, c9r1998choice, ?_, checked⟩
    intro S h
    simp only [c9r1998targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 14 _ (by rfl)
  have c9r1999_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r1999targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1999choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1999targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r1999choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r1999targets, c9r1999choice, ?_, checked⟩
    intro S h
    simp only [c9r1999targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1992_closed
  · subst row; exact c9r1993_closed
  · subst row; exact c9r1994_closed
  · subst row; exact c9r1995_closed
  · subst row; exact c9r1996_closed
  · subst row; exact c9r1997_closed
  · subst row; exact c9r1998_closed
  · subst row; exact c9r1999_closed
theorem C9R01984G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2000_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r2000targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r2000choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2000targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r2000choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2000targets, c9r2000choice, ?_, checked⟩
    intro S h
    simp only [c9r2000targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 23 _ (by rfl)
  have c9r2001_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r2001targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r2001choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2001targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r2001choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2001targets, c9r2001choice, ?_, checked⟩
    intro S h
    simp only [c9r2001targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 25 _ (by rfl)
  have c9r2002_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r2002targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r2002choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2002targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r2002choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2002targets, c9r2002choice, ?_, checked⟩
    intro S h
    simp only [c9r2002targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 27 _ (by rfl)
  have c9r2003_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r2003targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r2003choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,5),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2003targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)] c9r2003choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2003targets, c9r2003choice, ?_, checked⟩
    intro S h
    simp only [c9r2003targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 1 _ (by rfl)
  have c9r2004_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r2004targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r2004choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2004targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)] c9r2004choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2004targets, c9r2004choice, ?_, checked⟩
    intro S h
    simp only [c9r2004targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 5 _ (by rfl)
  have c9r2005_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r2005targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r2005choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2005targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)] c9r2005choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2005targets, c9r2005choice, ?_, checked⟩
    intro S h
    simp only [c9r2005targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 7 _ (by rfl)
  have c9r2006_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r2006targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r2006choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2006targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)] c9r2006choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2006targets, c9r2006choice, ?_, checked⟩
    intro S h
    simp only [c9r2006targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 9 _ (by rfl)
  have c9r2007_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r2007targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r2007choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2007targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] c9r2007choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2007targets, c9r2007choice, ?_, checked⟩
    intro S h
    simp only [c9r2007targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2000_closed
  · subst row; exact c9r2001_closed
  · subst row; exact c9r2002_closed
  · subst row; exact c9r2003_closed
  · subst row; exact c9r2004_closed
  · subst row; exact c9r2005_closed
  · subst row; exact c9r2006_closed
  · subst row; exact c9r2007_closed
theorem C9R01984G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2008_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r2008targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r2008choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2008targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)] c9r2008choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2008targets, c9r2008choice, ?_, checked⟩
    intro S h
    simp only [c9r2008targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 15 _ (by rfl)
  have c9r2009_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r2009targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r2009choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2009targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)] c9r2009choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2009targets, c9r2009choice, ?_, checked⟩
    intro S h
    simp only [c9r2009targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 18 _ (by rfl)
  have c9r2010_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r2010targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r2010choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2010targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)] c9r2010choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2010targets, c9r2010choice, ?_, checked⟩
    intro S h
    simp only [c9r2010targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 21 _ (by rfl)
  have c9r2011_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r2011targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r2011choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2011targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)] c9r2011choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2011targets, c9r2011choice, ?_, checked⟩
    intro S h
    simp only [c9r2011targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 24 _ (by rfl)
  have c9r2012_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r2012targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r2012choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,6),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0))),((4,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2012targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)] c9r2012choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2012targets, c9r2012choice, ?_, checked⟩
    intro S h
    simp only [c9r2012targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 29 _ (by rfl)
  have c9r2013_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r2013targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r2013choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2013targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)] c9r2013choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2013targets, c9r2013choice, ?_, checked⟩
    intro S h
    simp only [c9r2013targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,true] 1 _ (by rfl)
  have c9r2014_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r2014targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r2014choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2014targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)] c9r2014choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2014targets, c9r2014choice, ?_, checked⟩
    intro S h
    simp only [c9r2014targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,true] 3 _ (by rfl)
  have c9r2015_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r2015targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r2015choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((4,5),(13,(0,0))),((5,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2015targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)] c9r2015choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2015targets, c9r2015choice, ?_, checked⟩
    intro S h
    simp only [c9r2015targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,false,true,false,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2008_closed
  · subst row; exact c9r2009_closed
  · subst row; exact c9r2010_closed
  · subst row; exact c9r2011_closed
  · subst row; exact c9r2012_closed
  · subst row; exact c9r2013_closed
  · subst row; exact c9r2014_closed
  · subst row; exact c9r2015_closed
theorem C9R01984_closed (row : List GridPoint) (h : FamilyMember row F9B000L62) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L62, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R01984G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01984G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01984G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01984G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01984G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01984G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01984G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01984G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01984G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01984G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01984G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01984G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01984G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01984G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01984G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01984G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01984G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01984G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01984G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01984G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01984G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01984G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01984G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01984G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01984G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01984G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01984G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01984G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01984G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01984G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01984G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01984G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
