import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_144 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(3,2)]
def row6_144choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(537,(1,0))),((0,0),(135,(0,0))),((0,2),(390,(0,0))),((1,-1),(618,(0,1))),((1,3),(450,(0,0))),((2,0),(458,(0,0))),((2,1),(463,(0,0))),((2,3),(468,(0,0))),((3,1),(470,(0,0))),((3,3),(471,(0,0))),((4,2),(472,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_144_checked : successorFastRowCheck layer7 row6_144 row6_144choice = true := by decide
def row6_145 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2)]
def row6_145choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(538,(1,0))),((0,0),(136,(0,0))),((0,2),(391,(0,0))),((1,-1),(627,(0,1))),((1,2),(453,(0,0))),((2,-1),(650,(0,1))),((2,3),(474,(0,0))),((3,0),(475,(0,0))),((3,1),(476,(0,0))),((3,2),(477,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_145_checked : successorFastRowCheck layer7 row6_145 row6_145choice = true := by decide
def row6_146 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,0)]
def row6_146choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(539,(1,0))),((0,0),(137,(0,0))),((0,2),(392,(0,0))),((1,-1),(628,(0,1))),((1,2),(454,(0,0))),((2,-1),(652,(0,1))),((2,2),(475,(0,0))),((3,-1),(658,(0,1))),((3,1),(478,(0,0))),((4,0),(479,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_146_checked : successorFastRowCheck layer7 row6_146 row6_146choice = true := by decide
def row6_147 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,1)]
def row6_147choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(540,(1,0))),((0,0),(138,(0,0))),((0,2),(393,(0,0))),((1,-1),(629,(0,1))),((1,2),(455,(0,0))),((2,-1),(653,(0,1))),((2,2),(476,(0,0))),((3,0),(478,(0,0))),((3,2),(480,(0,0))),((4,1),(481,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_147_checked : successorFastRowCheck layer7 row6_147 row6_147choice = true := by decide
def row6_148 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(3,1)]
def row6_148choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(541,(1,0))),((0,0),(139,(0,0))),((0,2),(394,(0,0))),((1,-1),(631,(0,1))),((1,2),(459,(0,0))),((2,-1),(656,(0,1))),((2,1),(478,(0,0))),((3,-1),(659,(0,1))),((3,2),(482,(0,0))),((4,0),(483,(0,0))),((4,1),(484,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_148_checked : successorFastRowCheck layer7 row6_148 row6_148choice = true := by decide
def row6_149 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(4,0)]
def row6_149choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(542,(1,0))),((0,0),(140,(0,0))),((0,2),(395,(0,0))),((1,-1),(632,(0,1))),((1,2),(460,(0,0))),((2,-1),(657,(0,1))),((2,1),(479,(0,0))),((3,-1),(661,(0,1))),((3,1),(483,(0,0))),((4,-1),(662,(0,1))),((4,1),(485,(0,0))),((5,0),(486,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_149_checked : successorFastRowCheck layer7 row6_149 row6_149choice = true := by decide
def row6_150 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3)]
def row6_150choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(543,(1,0))),((0,0),(141,(0,0))),((0,2),(396,(0,0))),((1,-1),(633,(0,1))),((1,2),(461,(0,0))),((1,3),(473,(0,0))),((2,0),(474,(0,0))),((2,4),(487,(0,0))),((3,1),(488,(0,0))),((3,2),(489,(0,0))),((3,3),(490,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_150_checked : successorFastRowCheck layer7 row6_150 row6_150choice = true := by decide
def row6_151 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1)]
def row6_151choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(544,(1,0))),((0,0),(142,(0,0))),((0,2),(397,(0,0))),((1,-1),(634,(0,1))),((1,2),(462,(0,0))),((2,0),(476,(0,0))),((2,3),(488,(0,0))),((3,0),(491,(0,0))),((3,2),(492,(0,0))),((4,1),(493,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_151_checked : successorFastRowCheck layer7 row6_151 row6_151choice = true := by decide
def Closure6C018rows : List (List GridPoint) := [row6_144,row6_145,row6_146,row6_147,row6_148,row6_149,row6_150,row6_151]
theorem Closure6C018_closed : ∀ row ∈ Closure6C018rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C018rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_144choice,row6_144_checked⟩
  · subst row
    exact ⟨row6_145choice,row6_145_checked⟩
  · subst row
    exact ⟨row6_146choice,row6_146_checked⟩
  · subst row
    exact ⟨row6_147choice,row6_147_checked⟩
  · subst row
    exact ⟨row6_148choice,row6_148_checked⟩
  · subst row
    exact ⟨row6_149choice,row6_149_checked⟩
  · subst row
    exact ⟨row6_150choice,row6_150_checked⟩
  · subst row
    exact ⟨row6_151choice,row6_151_checked⟩
end Polyomino57
