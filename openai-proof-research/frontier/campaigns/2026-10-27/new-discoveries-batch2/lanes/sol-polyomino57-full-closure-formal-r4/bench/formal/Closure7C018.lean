import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_144 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1)]
def row7_144choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(937,(1,0))),((-1,1),(1603,(1,0))),((0,-1),(286,(0,1))),((0,2),(214,(0,0))),((1,-1),(1284,(0,1))),((1,2),(439,(0,0))),((2,0),(453,(0,0))),((2,2),(466,(0,0))),((3,-1),(1343,(0,1))),((3,2),(471,(0,0))),((4,0),(472,(0,0))),((4,1),(473,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_144_checked : successorFastRowCheck layer8 row7_144 row7_144choice = true := by decide
def row7_145 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2)]
def row7_145choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(938,(1,0))),((-1,1),(1604,(1,0))),((0,-1),(287,(0,1))),((0,2),(215,(0,0))),((1,-1),(1285,(0,1))),((1,2),(440,(0,0))),((2,0),(455,(0,0))),((2,2),(467,(0,0))),((3,0),(471,(0,0))),((3,3),(474,(0,0))),((4,1),(475,(0,0))),((4,2),(476,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_145_checked : successorFastRowCheck layer8 row7_145 row7_145choice = true := by decide
def row7_146 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1)]
def row7_146choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(939,(1,0))),((-1,1),(1605,(1,0))),((0,-1),(288,(0,1))),((0,2),(216,(0,0))),((1,-1),(1286,(0,1))),((1,2),(441,(0,0))),((2,0),(456,(0,0))),((2,2),(468,(0,0))),((3,0),(473,(0,0))),((3,2),(475,(0,0))),((4,0),(477,(0,0))),((4,2),(478,(0,0))),((5,1),(479,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_146_checked : successorFastRowCheck layer8 row7_146 row7_146choice = true := by decide
def row7_147 : List GridPoint := [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2)]
def row7_147choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(940,(1,0))),((-1,1),(1606,(1,0))),((0,-1),(289,(0,1))),((0,2),(231,(0,0))),((1,-1),(1287,(0,1))),((1,1),(428,(0,0))),((1,3),(480,(0,0))),((2,-1),(1344,(0,1))),((2,3),(481,(0,0))),((3,0),(482,(0,0))),((3,1),(483,(0,0))),((3,2),(484,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_147_checked : successorFastRowCheck layer8 row7_147 row7_147choice = true := by decide
def row7_148 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3)]
def row7_148choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(941,(1,0))),((-1,1),(1607,(1,0))),((0,-1),(298,(0,1))),((0,2),(248,(0,0))),((1,-1),(1301,(0,1))),((1,1),(449,(0,0))),((1,2),(481,(0,0))),((1,3),(485,(0,0))),((2,-1),(1345,(0,1))),((2,4),(486,(0,0))),((3,0),(487,(0,0))),((3,1),(488,(0,0))),((3,2),(489,(0,0))),((3,3),(490,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_148_checked : successorFastRowCheck layer8 row7_148 row7_148choice = true := by decide
def row7_149 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0)]
def row7_149choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(942,(1,0))),((-1,1),(1608,(1,0))),((0,-1),(299,(0,1))),((0,2),(249,(0,0))),((1,-1),(1302,(0,1))),((1,1),(450,(0,0))),((1,2),(482,(0,0))),((2,-1),(1347,(0,1))),((2,3),(487,(0,0))),((3,-1),(1368,(0,1))),((3,1),(491,(0,0))),((3,2),(492,(0,0))),((4,0),(493,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_149_checked : successorFastRowCheck layer8 row7_149 row7_149choice = true := by decide
def row7_150 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1)]
def row7_150choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(943,(1,0))),((-1,1),(1609,(1,0))),((0,-1),(300,(0,1))),((0,2),(250,(0,0))),((1,-1),(1303,(0,1))),((1,1),(451,(0,0))),((1,2),(483,(0,0))),((2,-1),(1348,(0,1))),((2,3),(488,(0,0))),((3,0),(491,(0,0))),((3,2),(494,(0,0))),((4,1),(495,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_150_checked : successorFastRowCheck layer8 row7_150 row7_150choice = true := by decide
def row7_151 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2)]
def row7_151choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(944,(1,0))),((-1,1),(1610,(1,0))),((0,-1),(301,(0,1))),((0,2),(251,(0,0))),((1,-1),(1304,(0,1))),((1,1),(452,(0,0))),((1,2),(484,(0,0))),((2,-1),(1349,(0,1))),((2,3),(489,(0,0))),((3,0),(492,(0,0))),((3,1),(494,(0,0))),((3,3),(496,(0,0))),((4,2),(497,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_151_checked : successorFastRowCheck layer8 row7_151 row7_151choice = true := by decide
def Closure7C018rows : List (List GridPoint) := [row7_144,row7_145,row7_146,row7_147,row7_148,row7_149,row7_150,row7_151]
theorem Closure7C018_closed : ∀ row ∈ Closure7C018rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C018rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_144choice,row7_144_checked⟩
  · subst row
    exact ⟨row7_145choice,row7_145_checked⟩
  · subst row
    exact ⟨row7_146choice,row7_146_checked⟩
  · subst row
    exact ⟨row7_147choice,row7_147_checked⟩
  · subst row
    exact ⟨row7_148choice,row7_148_checked⟩
  · subst row
    exact ⟨row7_149choice,row7_149_checked⟩
  · subst row
    exact ⟨row7_150choice,row7_150_checked⟩
  · subst row
    exact ⟨row7_151choice,row7_151_checked⟩
end Polyomino57
