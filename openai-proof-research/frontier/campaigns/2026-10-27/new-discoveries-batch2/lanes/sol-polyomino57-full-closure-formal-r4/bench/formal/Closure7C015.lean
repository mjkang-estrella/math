import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_120 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1)]
def row7_120choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(913,(1,0))),((-1,1),(1579,(1,0))),((-1,3),(2500,(1,0))),((0,-1),(190,(0,1))),((0,2),(120,(0,0))),((0,4),(381,(0,0))),((1,0),(386,(0,0))),((1,4),(390,(0,0))),((2,0),(394,(0,0))),((2,2),(395,(0,0))),((2,3),(396,(0,0))),((3,1),(397,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_120_checked : successorFastRowCheck layer8 row7_120 row7_120choice = true := by decide
def row7_121 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2)]
def row7_121choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(914,(1,0))),((-1,1),(1580,(1,0))),((-1,3),(2501,(1,0))),((0,-1),(191,(0,1))),((0,2),(121,(0,0))),((0,4),(382,(0,0))),((1,0),(387,(0,0))),((1,4),(391,(0,0))),((2,1),(395,(0,0))),((2,3),(398,(0,0))),((3,2),(399,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_121_checked : successorFastRowCheck layer8 row7_121 row7_121choice = true := by decide
def row7_122 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3)]
def row7_122choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(915,(1,0))),((-1,1),(1581,(1,0))),((-1,3),(2502,(1,0))),((0,-1),(192,(0,1))),((0,2),(122,(0,0))),((0,4),(383,(0,0))),((1,0),(388,(0,0))),((1,4),(392,(0,0))),((2,1),(396,(0,0))),((2,2),(398,(0,0))),((2,4),(400,(0,0))),((3,3),(401,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_122_checked : successorFastRowCheck layer8 row7_122 row7_122choice = true := by decide
def row7_123 : List GridPoint := [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4)]
def row7_123choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(916,(1,0))),((-1,1),(1582,(1,0))),((-1,4),(2669,(1,0))),((0,-1),(193,(0,1))),((0,2),(188,(0,0))),((0,3),(380,(0,0))),((0,5),(403,(0,0))),((1,0),(404,(0,0))),((1,5),(405,(0,0))),((2,1),(406,(0,0))),((2,2),(407,(0,0))),((2,3),(408,(0,0))),((2,4),(409,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_123_checked : successorFastRowCheck layer8 row7_123 row7_123choice = true := by decide
def row7_124 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_124choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(917,(1,0))),((-1,1),(1583,(1,0))),((0,-1),(261,(0,1))),((0,2),(194,(0,0))),((0,3),(384,(0,0))),((0,4),(404,(0,0))),((1,-1),(1250,(0,1))),((1,5),(411,(0,0))),((2,0),(412,(0,0))),((2,1),(413,(0,0))),((2,2),(414,(0,0))),((2,3),(415,(0,0))),((2,4),(416,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_124_checked : successorFastRowCheck layer8 row7_124 row7_124choice = true := by decide
def row7_125 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row7_125choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(918,(1,0))),((-1,1),(1584,(1,0))),((0,-1),(262,(0,1))),((0,2),(195,(0,0))),((0,3),(385,(0,0))),((1,-1),(1252,(0,1))),((1,4),(412,(0,0))),((2,-1),(1324,(0,1))),((2,1),(417,(0,0))),((2,2),(418,(0,0))),((2,3),(419,(0,0))),((3,0),(420,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_125_checked : successorFastRowCheck layer8 row7_125 row7_125choice = true := by decide
def row7_126 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row7_126choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(919,(1,0))),((-1,1),(1585,(1,0))),((0,-1),(263,(0,1))),((0,2),(196,(0,0))),((0,3),(386,(0,0))),((1,-1),(1253,(0,1))),((1,4),(413,(0,0))),((2,0),(417,(0,0))),((2,2),(421,(0,0))),((2,3),(422,(0,0))),((3,1),(423,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_126_checked : successorFastRowCheck layer8 row7_126 row7_126choice = true := by decide
def row7_127 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row7_127choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(920,(1,0))),((-1,1),(1586,(1,0))),((0,-1),(264,(0,1))),((0,2),(197,(0,0))),((0,3),(387,(0,0))),((1,-1),(1254,(0,1))),((1,4),(414,(0,0))),((2,0),(418,(0,0))),((2,1),(421,(0,0))),((2,3),(424,(0,0))),((3,2),(425,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_127_checked : successorFastRowCheck layer8 row7_127 row7_127choice = true := by decide
def Closure7C015rows : List (List GridPoint) := [row7_120,row7_121,row7_122,row7_123,row7_124,row7_125,row7_126,row7_127]
theorem Closure7C015_closed : ∀ row ∈ Closure7C015rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C015rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_120choice,row7_120_checked⟩
  · subst row
    exact ⟨row7_121choice,row7_121_checked⟩
  · subst row
    exact ⟨row7_122choice,row7_122_checked⟩
  · subst row
    exact ⟨row7_123choice,row7_123_checked⟩
  · subst row
    exact ⟨row7_124choice,row7_124_checked⟩
  · subst row
    exact ⟨row7_125choice,row7_125_checked⟩
  · subst row
    exact ⟨row7_126choice,row7_126_checked⟩
  · subst row
    exact ⟨row7_127choice,row7_127_checked⟩
end Polyomino57
