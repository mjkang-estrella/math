import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_208 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row6_208choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(741,(1,0))),((0,0),(236,(0,0))),((0,1),(430,(0,0))),((0,2),(576,(0,0))),((0,4),(698,(0,0))),((1,-1),(751,(0,1))),((1,4),(706,(0,0))),((2,-1),(755,(0,1))),((2,1),(711,(0,0))),((2,2),(712,(0,0))),((2,3),(713,(0,0))),((3,0),(714,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_208_checked : successorFastRowCheck layer7 row6_208 row6_208choice = true := by decide
def row6_209 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row6_209choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(742,(1,0))),((0,0),(237,(0,0))),((0,1),(431,(0,0))),((0,2),(577,(0,0))),((0,4),(699,(0,0))),((1,-1),(752,(0,1))),((1,4),(707,(0,0))),((2,0),(711,(0,0))),((2,2),(715,(0,0))),((2,3),(716,(0,0))),((3,1),(717,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_209_checked : successorFastRowCheck layer7 row6_209 row6_209choice = true := by decide
def row6_210 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row6_210choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(743,(1,0))),((0,0),(238,(0,0))),((0,1),(432,(0,0))),((0,2),(578,(0,0))),((0,4),(700,(0,0))),((1,-1),(753,(0,1))),((1,4),(708,(0,0))),((2,0),(712,(0,0))),((2,1),(715,(0,0))),((2,3),(718,(0,0))),((3,2),(719,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_210_checked : successorFastRowCheck layer7 row6_210 row6_210choice = true := by decide
def row6_211 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row6_211choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(744,(1,0))),((0,0),(239,(0,0))),((0,1),(433,(0,0))),((0,2),(579,(0,0))),((0,4),(701,(0,0))),((1,-1),(754,(0,1))),((1,4),(709,(0,0))),((2,0),(713,(0,0))),((2,1),(716,(0,0))),((2,2),(718,(0,0))),((2,4),(720,(0,0))),((3,3),(721,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_211_checked : successorFastRowCheck layer7 row6_211 row6_211choice = true := by decide
def row6_212 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row6_212choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(745,(1,0))),((0,1),(434,(0,0))),((0,2),(588,(0,0))),((0,4),(702,(0,0))),((1,0),(711,(0,0))),((1,4),(725,(0,0))),((2,-1),(756,(0,1))),((2,2),(726,(0,0))),((2,3),(727,(0,0))),((3,0),(728,(0,0))),((3,1),(729,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_212_checked : successorFastRowCheck layer7 row6_212 row6_212choice = true := by decide
def row6_213 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row6_213choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(746,(1,0))),((0,2),(593,(0,0))),((0,4),(703,(0,0))),((1,0),(723,(0,0))),((1,1),(726,(0,0))),((1,4),(732,(0,0))),((2,-1),(757,(0,1))),((2,3),(733,(0,0))),((3,0),(734,(0,0))),((3,1),(735,(0,0))),((3,2),(736,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_213_checked : successorFastRowCheck layer7 row6_213 row6_213choice = true := by decide
def row6_214 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row6_214choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(747,(1,0))),((0,2),(600,(0,0))),((0,4),(704,(0,0))),((1,0),(724,(0,0))),((1,1),(731,(0,0))),((1,2),(733,(0,0))),((1,4),(739,(0,0))),((2,-1),(758,(0,1))),((2,4),(740,(0,0))),((3,0),(741,(0,0))),((3,1),(742,(0,0))),((3,2),(743,(0,0))),((3,3),(744,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_214_checked : successorFastRowCheck layer7 row6_214 row6_214choice = true := by decide
def row6_215 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row6_215choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(758,(1,0))),((0,0),(240,(0,0))),((0,1),(435,(0,0))),((0,2),(601,(0,0))),((0,3),(697,(0,0))),((0,5),(748,(0,0))),((1,-1),(759,(0,1))),((1,5),(749,(0,0))),((2,0),(750,(0,0))),((2,1),(751,(0,0))),((2,2),(752,(0,0))),((2,3),(753,(0,0))),((2,4),(754,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_215_checked : successorFastRowCheck layer7 row6_215 row6_215choice = true := by decide
def Closure6C026rows : List (List GridPoint) := [row6_208,row6_209,row6_210,row6_211,row6_212,row6_213,row6_214,row6_215]
theorem Closure6C026_closed : ∀ row ∈ Closure6C026rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C026rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_208choice,row6_208_checked⟩
  · subst row
    exact ⟨row6_209choice,row6_209_checked⟩
  · subst row
    exact ⟨row6_210choice,row6_210_checked⟩
  · subst row
    exact ⟨row6_211choice,row6_211_checked⟩
  · subst row
    exact ⟨row6_212choice,row6_212_checked⟩
  · subst row
    exact ⟨row6_213choice,row6_213_checked⟩
  · subst row
    exact ⟨row6_214choice,row6_214_checked⟩
  · subst row
    exact ⟨row6_215choice,row6_215_checked⟩
end Polyomino57
