import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_176 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)]
def row6_176choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(666,(1,0))),((-1,3),(734,(1,0))),((0,0),(218,(0,0))),((0,1),(361,(0,0))),((0,4),(570,(0,0))),((1,-1),(699,(0,1))),((1,3),(576,(0,0))),((2,-1),(702,(0,1))),((2,1),(580,(0,0))),((2,2),(581,(0,0))),((3,0),(582,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_176_checked : successorFastRowCheck layer7 row6_176 row6_176choice = true := by decide
def row6_177 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)]
def row6_177choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(667,(1,0))),((-1,3),(735,(1,0))),((0,0),(219,(0,0))),((0,1),(362,(0,0))),((0,4),(571,(0,0))),((1,-1),(700,(0,1))),((1,3),(577,(0,0))),((2,0),(580,(0,0))),((2,2),(583,(0,0))),((3,1),(584,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_177_checked : successorFastRowCheck layer7 row6_177 row6_177choice = true := by decide
def row6_178 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)]
def row6_178choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(668,(1,0))),((-1,3),(736,(1,0))),((0,0),(220,(0,0))),((0,1),(363,(0,0))),((0,4),(572,(0,0))),((1,-1),(701,(0,1))),((1,3),(578,(0,0))),((2,0),(581,(0,0))),((2,1),(583,(0,0))),((2,3),(585,(0,0))),((3,2),(586,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_178_checked : successorFastRowCheck layer7 row6_178 row6_178choice = true := by decide
def row6_179 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)]
def row6_179choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(669,(1,0))),((-1,3),(737,(1,0))),((0,1),(372,(0,0))),((0,4),(573,(0,0))),((1,0),(580,(0,0))),((1,3),(588,(0,0))),((2,-1),(703,(0,1))),((2,2),(589,(0,0))),((3,0),(590,(0,0))),((3,1),(591,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_179_checked : successorFastRowCheck layer7 row6_179 row6_179choice = true := by decide
def row6_180 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2)]
def row6_180choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(670,(1,0))),((-1,3),(738,(1,0))),((0,1),(378,(0,0))),((0,4),(574,(0,0))),((1,0),(587,(0,0))),((1,1),(589,(0,0))),((1,3),(593,(0,0))),((2,-1),(704,(0,1))),((2,3),(594,(0,0))),((3,0),(595,(0,0))),((3,1),(596,(0,0))),((3,2),(597,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_180_checked : successorFastRowCheck layer7 row6_180 row6_180choice = true := by decide
def row6_181 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row6_181choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(671,(1,0))),((0,0),(221,(0,0))),((0,1),(379,(0,0))),((0,3),(575,(0,0))),((0,4),(601,(0,0))),((1,-1),(705,(0,1))),((1,5),(602,(0,0))),((2,0),(603,(0,0))),((2,1),(604,(0,0))),((2,2),(605,(0,0))),((2,3),(606,(0,0))),((2,4),(607,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_181_checked : successorFastRowCheck layer7 row6_181 row6_181choice = true := by decide
def row6_182 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row6_182choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(672,(1,0))),((0,0),(222,(0,0))),((0,1),(380,(0,0))),((0,3),(576,(0,0))),((1,-1),(707,(0,1))),((1,4),(603,(0,0))),((2,-1),(725,(0,1))),((2,1),(608,(0,0))),((2,2),(609,(0,0))),((2,3),(610,(0,0))),((3,0),(611,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_182_checked : successorFastRowCheck layer7 row6_182 row6_182choice = true := by decide
def row6_183 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row6_183choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(673,(1,0))),((0,0),(223,(0,0))),((0,1),(381,(0,0))),((0,3),(577,(0,0))),((1,-1),(708,(0,1))),((1,4),(604,(0,0))),((2,0),(608,(0,0))),((2,2),(612,(0,0))),((2,3),(613,(0,0))),((3,1),(614,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_183_checked : successorFastRowCheck layer7 row6_183 row6_183choice = true := by decide
def Closure6C022rows : List (List GridPoint) := [row6_176,row6_177,row6_178,row6_179,row6_180,row6_181,row6_182,row6_183]
theorem Closure6C022_closed : ∀ row ∈ Closure6C022rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C022rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_176choice,row6_176_checked⟩
  · subst row
    exact ⟨row6_177choice,row6_177_checked⟩
  · subst row
    exact ⟨row6_178choice,row6_178_checked⟩
  · subst row
    exact ⟨row6_179choice,row6_179_checked⟩
  · subst row
    exact ⟨row6_180choice,row6_180_checked⟩
  · subst row
    exact ⟨row6_181choice,row6_181_checked⟩
  · subst row
    exact ⟨row6_182choice,row6_182_checked⟩
  · subst row
    exact ⟨row6_183choice,row6_183_checked⟩
end Polyomino57
