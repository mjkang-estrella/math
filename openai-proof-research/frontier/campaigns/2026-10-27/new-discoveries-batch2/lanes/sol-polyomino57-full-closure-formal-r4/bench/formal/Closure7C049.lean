import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_392 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)]
def row7_392choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1714,(1,0))),((-1,2),(2221,(1,0))),((0,0),(207,(0,0))),((0,3),(1206,(0,0))),((1,-1),(1957,(0,1))),((1,2),(1268,(0,0))),((2,-1),(1983,(0,1))),((2,2),(1289,(0,0))),((3,-1),(1989,(0,1))),((3,1),(1292,(0,0))),((4,0),(1293,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_392_checked : successorFastRowCheck layer8 row7_392 row7_392choice = true := by decide
def row7_393 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)]
def row7_393choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1715,(1,0))),((-1,2),(2222,(1,0))),((0,0),(208,(0,0))),((0,3),(1207,(0,0))),((1,-1),(1958,(0,1))),((1,2),(1269,(0,0))),((2,-1),(1984,(0,1))),((2,2),(1290,(0,0))),((3,0),(1292,(0,0))),((3,2),(1294,(0,0))),((4,1),(1295,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_393_checked : successorFastRowCheck layer8 row7_393 row7_393choice = true := by decide
def row7_394 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1)]
def row7_394choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1716,(1,0))),((-1,2),(2223,(1,0))),((0,0),(209,(0,0))),((0,3),(1208,(0,0))),((1,-1),(1960,(0,1))),((1,2),(1273,(0,0))),((2,-1),(1987,(0,1))),((2,1),(1292,(0,0))),((3,-1),(1990,(0,1))),((3,2),(1296,(0,0))),((4,0),(1297,(0,0))),((4,1),(1298,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_394_checked : successorFastRowCheck layer8 row7_394 row7_394choice = true := by decide
def row7_395 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0)]
def row7_395choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1717,(1,0))),((-1,2),(2224,(1,0))),((0,0),(210,(0,0))),((0,3),(1209,(0,0))),((1,-1),(1961,(0,1))),((1,2),(1274,(0,0))),((2,-1),(1988,(0,1))),((2,1),(1293,(0,0))),((3,-1),(1992,(0,1))),((3,1),(1297,(0,0))),((4,-1),(1993,(0,1))),((4,1),(1299,(0,0))),((5,0),(1300,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_395_checked : successorFastRowCheck layer8 row7_395 row7_395choice = true := by decide
def row7_396 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3)]
def row7_396choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1718,(1,0))),((-1,2),(2225,(1,0))),((0,0),(211,(0,0))),((0,3),(1210,(0,0))),((1,-1),(1962,(0,1))),((1,2),(1275,(0,0))),((1,3),(1287,(0,0))),((2,0),(1288,(0,0))),((2,4),(1301,(0,0))),((3,1),(1302,(0,0))),((3,2),(1303,(0,0))),((3,3),(1304,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_396_checked : successorFastRowCheck layer8 row7_396 row7_396choice = true := by decide
def row7_397 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)]
def row7_397choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1719,(1,0))),((-1,2),(2226,(1,0))),((0,0),(212,(0,0))),((0,3),(1211,(0,0))),((1,-1),(1963,(0,1))),((1,2),(1276,(0,0))),((2,0),(1290,(0,0))),((2,3),(1302,(0,0))),((3,0),(1305,(0,0))),((3,2),(1306,(0,0))),((4,1),(1307,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_397_checked : successorFastRowCheck layer8 row7_397 row7_397choice = true := by decide
def row7_398 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2)]
def row7_398choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1720,(1,0))),((-1,2),(2227,(1,0))),((0,0),(213,(0,0))),((0,3),(1212,(0,0))),((1,-1),(1964,(0,1))),((1,2),(1277,(0,0))),((2,0),(1291,(0,0))),((2,3),(1303,(0,0))),((3,1),(1306,(0,0))),((3,3),(1308,(0,0))),((4,2),(1309,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_398_checked : successorFastRowCheck layer8 row7_398 row7_398choice = true := by decide
def row7_399 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1)]
def row7_399choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1721,(1,0))),((-1,2),(2228,(1,0))),((0,0),(214,(0,0))),((0,3),(1213,(0,0))),((1,-1),(1965,(0,1))),((1,2),(1278,(0,0))),((2,0),(1292,(0,0))),((2,2),(1305,(0,0))),((3,-1),(1994,(0,1))),((3,2),(1310,(0,0))),((4,0),(1311,(0,0))),((4,1),(1312,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_399_checked : successorFastRowCheck layer8 row7_399 row7_399choice = true := by decide
def Closure7C049rows : List (List GridPoint) := [row7_392,row7_393,row7_394,row7_395,row7_396,row7_397,row7_398,row7_399]
theorem Closure7C049_closed : ∀ row ∈ Closure7C049rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C049rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_392choice,row7_392_checked⟩
  · subst row
    exact ⟨row7_393choice,row7_393_checked⟩
  · subst row
    exact ⟨row7_394choice,row7_394_checked⟩
  · subst row
    exact ⟨row7_395choice,row7_395_checked⟩
  · subst row
    exact ⟨row7_396choice,row7_396_checked⟩
  · subst row
    exact ⟨row7_397choice,row7_397_checked⟩
  · subst row
    exact ⟨row7_398choice,row7_398_checked⟩
  · subst row
    exact ⟨row7_399choice,row7_399_checked⟩
end Polyomino57
