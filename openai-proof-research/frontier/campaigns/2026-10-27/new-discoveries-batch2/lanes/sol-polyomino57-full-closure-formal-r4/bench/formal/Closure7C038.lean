import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_304 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)]
def row7_304choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1097,(1,0))),((0,-1),(606,(0,1))),((0,1),(474,(0,0))),((1,-1),(1570,(0,1))),((1,2),(885,(0,0))),((2,0),(934,(0,0))),((2,2),(970,(0,0))),((2,3),(982,(0,0))),((3,0),(983,(0,0))),((3,4),(991,(0,0))),((4,1),(992,(0,0))),((4,2),(993,(0,0))),((4,3),(994,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_304_checked : successorFastRowCheck layer8 row7_304 row7_304choice = true := by decide
def row7_305 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)]
def row7_305choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1098,(1,0))),((0,-1),(607,(0,1))),((0,1),(475,(0,0))),((1,-1),(1571,(0,1))),((1,2),(886,(0,0))),((2,0),(935,(0,0))),((2,2),(971,(0,0))),((3,0),(985,(0,0))),((3,3),(992,(0,0))),((4,0),(995,(0,0))),((4,2),(996,(0,0))),((5,1),(997,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_305_checked : successorFastRowCheck layer8 row7_305 row7_305choice = true := by decide
def row7_306 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]
def row7_306choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1099,(1,0))),((0,-1),(608,(0,1))),((0,1),(476,(0,0))),((1,-1),(1572,(0,1))),((1,2),(887,(0,0))),((2,0),(936,(0,0))),((2,2),(972,(0,0))),((3,0),(986,(0,0))),((3,3),(993,(0,0))),((4,1),(996,(0,0))),((4,3),(998,(0,0))),((5,2),(999,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_306_checked : successorFastRowCheck layer8 row7_306 row7_306choice = true := by decide
def row7_307 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)]
def row7_307choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1100,(1,0))),((0,-1),(609,(0,1))),((0,1),(477,(0,0))),((1,-1),(1573,(0,1))),((1,2),(888,(0,0))),((2,0),(937,(0,0))),((2,2),(973,(0,0))),((3,0),(987,(0,0))),((3,2),(995,(0,0))),((4,-1),(1749,(0,1))),((4,2),(1000,(0,0))),((5,0),(1001,(0,0))),((5,1),(1002,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_307_checked : successorFastRowCheck layer8 row7_307 row7_307choice = true := by decide
def row7_308 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)]
def row7_308choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1101,(1,0))),((0,-1),(610,(0,1))),((0,1),(478,(0,0))),((1,-1),(1574,(0,1))),((1,2),(889,(0,0))),((2,0),(938,(0,0))),((2,2),(974,(0,0))),((3,0),(989,(0,0))),((3,2),(996,(0,0))),((4,0),(1000,(0,0))),((4,3),(1003,(0,0))),((5,1),(1004,(0,0))),((5,2),(1005,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_308_checked : successorFastRowCheck layer8 row7_308 row7_308choice = true := by decide
def row7_309 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]
def row7_309choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1102,(1,0))),((0,-1),(611,(0,1))),((0,1),(479,(0,0))),((1,-1),(1575,(0,1))),((1,2),(890,(0,0))),((2,0),(939,(0,0))),((2,2),(975,(0,0))),((3,0),(990,(0,0))),((3,2),(997,(0,0))),((4,0),(1002,(0,0))),((4,2),(1004,(0,0))),((5,0),(1006,(0,0))),((5,2),(1007,(0,0))),((6,1),(1008,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_309_checked : successorFastRowCheck layer8 row7_309 row7_309choice = true := by decide
def row7_310 : List GridPoint := [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_310choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1103,(1,0))),((0,-1),(612,(0,1))),((0,1),(480,(0,0))),((0,2),(754,(0,0))),((0,3),(783,(0,0))),((1,-1),(1576,(0,1))),((1,1),(816,(0,0))),((1,4),(1009,(0,0))),((2,-1),(1750,(0,1))),((2,3),(1010,(0,0))),((3,0),(1011,(0,0))),((3,1),(1012,(0,0))),((3,2),(1013,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_310_checked : successorFastRowCheck layer8 row7_310 row7_310choice = true := by decide
def row7_311 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)]
def row7_311choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1104,(1,0))),((0,-1),(614,(0,1))),((0,1),(481,(0,0))),((0,2),(755,(0,0))),((1,-1),(1578,(0,1))),((1,1),(850,(0,0))),((1,3),(1010,(0,0))),((2,-1),(1751,(0,1))),((2,4),(1014,(0,0))),((3,0),(1015,(0,0))),((3,1),(1016,(0,0))),((3,2),(1017,(0,0))),((3,3),(1018,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_311_checked : successorFastRowCheck layer8 row7_311 row7_311choice = true := by decide
def Closure7C038rows : List (List GridPoint) := [row7_304,row7_305,row7_306,row7_307,row7_308,row7_309,row7_310,row7_311]
theorem Closure7C038_closed : ∀ row ∈ Closure7C038rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C038rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_304choice,row7_304_checked⟩
  · subst row
    exact ⟨row7_305choice,row7_305_checked⟩
  · subst row
    exact ⟨row7_306choice,row7_306_checked⟩
  · subst row
    exact ⟨row7_307choice,row7_307_checked⟩
  · subst row
    exact ⟨row7_308choice,row7_308_checked⟩
  · subst row
    exact ⟨row7_309choice,row7_309_checked⟩
  · subst row
    exact ⟨row7_310choice,row7_310_checked⟩
  · subst row
    exact ⟨row7_311choice,row7_311_checked⟩
end Polyomino57
