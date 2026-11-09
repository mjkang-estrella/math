import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_56 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2)]
def row6_56choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(297,(1,0))),((-1,1),(492,(1,0))),((0,-1),(103,(0,1))),((0,2),(85,(0,0))),((1,0),(132,(0,0))),((1,3),(167,(0,0))),((2,0),(174,(0,0))),((2,3),(177,(0,0))),((3,1),(178,(0,0))),((3,2),(179,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_56_checked : successorFastRowCheck layer7 row6_56 row6_56choice = true := by decide
def row6_57 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1)]
def row6_57choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(298,(1,0))),((-1,1),(493,(1,0))),((0,-1),(104,(0,1))),((0,2),(86,(0,0))),((1,0),(133,(0,0))),((1,3),(169,(0,0))),((2,0),(176,(0,0))),((2,2),(178,(0,0))),((3,0),(180,(0,0))),((3,2),(181,(0,0))),((4,1),(182,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_57_checked : successorFastRowCheck layer7 row6_57 row6_57choice = true := by decide
def row6_58 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3)]
def row6_58choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(299,(1,0))),((-1,1),(494,(1,0))),((0,-1),(105,(0,1))),((0,2),(87,(0,0))),((1,0),(134,(0,0))),((1,3),(170,(0,0))),((2,1),(177,(0,0))),((2,4),(183,(0,0))),((3,2),(184,(0,0))),((3,3),(185,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_58_checked : successorFastRowCheck layer7 row6_58 row6_58choice = true := by decide
def row6_59 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2)]
def row6_59choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(300,(1,0))),((-1,1),(495,(1,0))),((0,-1),(106,(0,1))),((0,2),(88,(0,0))),((1,0),(135,(0,0))),((1,3),(171,(0,0))),((2,1),(179,(0,0))),((2,3),(184,(0,0))),((3,1),(186,(0,0))),((3,3),(187,(0,0))),((4,2),(188,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_59_checked : successorFastRowCheck layer7 row6_59 row6_59choice = true := by decide
def row6_60 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2)]
def row6_60choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(301,(1,0))),((-1,1),(496,(1,0))),((0,-1),(108,(0,1))),((0,2),(89,(0,0))),((1,0),(136,(0,0))),((1,2),(174,(0,0))),((2,-1),(422,(0,1))),((2,3),(190,(0,0))),((3,0),(191,(0,0))),((3,1),(192,(0,0))),((3,2),(193,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_60_checked : successorFastRowCheck layer7 row6_60 row6_60choice = true := by decide
def row6_61 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0)]
def row6_61choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(302,(1,0))),((-1,1),(497,(1,0))),((0,-1),(109,(0,1))),((0,2),(90,(0,0))),((1,0),(137,(0,0))),((1,2),(175,(0,0))),((2,-1),(424,(0,1))),((2,2),(191,(0,0))),((3,-1),(426,(0,1))),((3,1),(194,(0,0))),((4,0),(195,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_61_checked : successorFastRowCheck layer7 row6_61 row6_61choice = true := by decide
def row6_62 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1)]
def row6_62choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(303,(1,0))),((-1,1),(498,(1,0))),((0,-1),(110,(0,1))),((0,2),(91,(0,0))),((1,0),(138,(0,0))),((1,2),(176,(0,0))),((2,-1),(425,(0,1))),((2,2),(192,(0,0))),((3,0),(194,(0,0))),((3,2),(196,(0,0))),((4,1),(197,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_62_checked : successorFastRowCheck layer7 row6_62 row6_62choice = true := by decide
def row6_63 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3)]
def row6_63choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(304,(1,0))),((-1,1),(499,(1,0))),((0,-1),(111,(0,1))),((0,2),(92,(0,0))),((1,0),(141,(0,0))),((1,2),(177,(0,0))),((1,3),(189,(0,0))),((2,0),(190,(0,0))),((2,4),(198,(0,0))),((3,1),(199,(0,0))),((3,2),(200,(0,0))),((3,3),(201,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_63_checked : successorFastRowCheck layer7 row6_63 row6_63choice = true := by decide
def Closure6C007rows : List (List GridPoint) := [row6_56,row6_57,row6_58,row6_59,row6_60,row6_61,row6_62,row6_63]
theorem Closure6C007_closed : ∀ row ∈ Closure6C007rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C007rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_56choice,row6_56_checked⟩
  · subst row
    exact ⟨row6_57choice,row6_57_checked⟩
  · subst row
    exact ⟨row6_58choice,row6_58_checked⟩
  · subst row
    exact ⟨row6_59choice,row6_59_checked⟩
  · subst row
    exact ⟨row6_60choice,row6_60_checked⟩
  · subst row
    exact ⟨row6_61choice,row6_61_checked⟩
  · subst row
    exact ⟨row6_62choice,row6_62_checked⟩
  · subst row
    exact ⟨row6_63choice,row6_63_checked⟩
end Polyomino57
