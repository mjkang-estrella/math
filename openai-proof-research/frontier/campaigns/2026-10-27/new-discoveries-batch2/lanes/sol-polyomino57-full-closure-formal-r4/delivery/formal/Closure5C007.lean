import Layer6
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row5_56 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3)]
def row5_56choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(200,(1,0))),((0,0),(70,(0,0))),((0,1),(118,(0,0))),((0,3),(175,(0,0))),((1,-1),(207,(0,1))),((1,4),(181,(0,0))),((2,0),(182,(0,0))),((2,1),(183,(0,0))),((2,2),(184,(0,0))),((2,3),(185,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_56_checked : successorFastRowCheck layer6 row5_56 row5_56choice = true := by decide
def row5_57 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0)]
def row5_57choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(201,(1,0))),((0,0),(71,(0,0))),((0,1),(119,(0,0))),((0,3),(176,(0,0))),((1,-1),(209,(0,1))),((1,3),(182,(0,0))),((2,-1),(212,(0,1))),((2,1),(186,(0,0))),((2,2),(187,(0,0))),((3,0),(188,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_57_checked : successorFastRowCheck layer6 row5_57 row5_57choice = true := by decide
def row5_58 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1)]
def row5_58choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(202,(1,0))),((0,0),(72,(0,0))),((0,1),(120,(0,0))),((0,3),(177,(0,0))),((1,-1),(210,(0,1))),((1,3),(183,(0,0))),((2,0),(186,(0,0))),((2,2),(189,(0,0))),((3,1),(190,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_58_checked : successorFastRowCheck layer6 row5_58 row5_58choice = true := by decide
def row5_59 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2)]
def row5_59choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(203,(1,0))),((0,0),(73,(0,0))),((0,1),(121,(0,0))),((0,3),(178,(0,0))),((1,-1),(211,(0,1))),((1,3),(184,(0,0))),((2,0),(187,(0,0))),((2,1),(189,(0,0))),((2,3),(191,(0,0))),((3,2),(192,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_59_checked : successorFastRowCheck layer6 row5_59 row5_59choice = true := by decide
def row5_60 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1)]
def row5_60choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(204,(1,0))),((0,1),(126,(0,0))),((0,3),(179,(0,0))),((1,0),(186,(0,0))),((1,3),(194,(0,0))),((2,-1),(213,(0,1))),((2,2),(195,(0,0))),((3,0),(196,(0,0))),((3,1),(197,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_60_checked : successorFastRowCheck layer6 row5_60 row5_60choice = true := by decide
def row5_61 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2)]
def row5_61choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(205,(1,0))),((0,1),(131,(0,0))),((0,3),(180,(0,0))),((1,0),(193,(0,0))),((1,1),(195,(0,0))),((1,3),(199,(0,0))),((2,-1),(214,(0,1))),((2,3),(200,(0,0))),((3,0),(201,(0,0))),((3,1),(202,(0,0))),((3,2),(203,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_61_checked : successorFastRowCheck layer6 row5_61 row5_61choice = true := by decide
def row5_62 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3)]
def row5_62choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(214,(1,0))),((0,0),(74,(0,0))),((0,1),(132,(0,0))),((0,2),(175,(0,0))),((0,4),(206,(0,0))),((1,-1),(215,(0,1))),((1,4),(207,(0,0))),((2,0),(208,(0,0))),((2,1),(209,(0,0))),((2,2),(210,(0,0))),((2,3),(211,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_62_checked : successorFastRowCheck layer6 row5_62 row5_62choice = true := by decide
def Closure5C007rows : List (List GridPoint) := [row5_56,row5_57,row5_58,row5_59,row5_60,row5_61,row5_62]
theorem Closure5C007_closed : ∀ row ∈ Closure5C007rows, ∃ choice, successorFastRowCheck layer6 row choice = true := by
  intro row hr
  simp only [Closure5C007rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst row
    exact ⟨row5_56choice,row5_56_checked⟩
  · subst row
    exact ⟨row5_57choice,row5_57_checked⟩
  · subst row
    exact ⟨row5_58choice,row5_58_checked⟩
  · subst row
    exact ⟨row5_59choice,row5_59_checked⟩
  · subst row
    exact ⟨row5_60choice,row5_60_checked⟩
  · subst row
    exact ⟨row5_61choice,row5_61_checked⟩
  · subst row
    exact ⟨row5_62choice,row5_62_checked⟩
end Polyomino57
