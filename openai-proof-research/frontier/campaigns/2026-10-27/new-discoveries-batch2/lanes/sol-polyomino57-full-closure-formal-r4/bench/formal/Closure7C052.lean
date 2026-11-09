import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_416 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1)]
def row7_416choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1738,(1,0))),((-1,2),(2245,(1,0))),((0,0),(302,(0,0))),((0,3),(1236,(0,0))),((1,0),(1305,(0,0))),((1,2),(1338,(0,0))),((2,0),(1350,(0,0))),((2,3),(1368,(0,0))),((3,-1),(2021,(0,1))),((3,2),(1369,(0,0))),((4,0),(1370,(0,0))),((4,1),(1371,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_416_checked : successorFastRowCheck layer8 row7_416 row7_416choice = true := by decide
def row7_417 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2)]
def row7_417choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1739,(1,0))),((-1,2),(2246,(1,0))),((0,0),(307,(0,0))),((0,3),(1237,(0,0))),((1,0),(1310,(0,0))),((1,2),(1339,(0,0))),((2,0),(1357,(0,0))),((2,2),(1369,(0,0))),((3,-1),(2022,(0,1))),((3,3),(1373,(0,0))),((4,0),(1374,(0,0))),((4,1),(1375,(0,0))),((4,2),(1376,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_417_checked : successorFastRowCheck layer8 row7_417 row7_417choice = true := by decide
def row7_418 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0)]
def row7_418choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1740,(1,0))),((-1,2),(2247,(1,0))),((0,0),(308,(0,0))),((0,3),(1238,(0,0))),((1,0),(1311,(0,0))),((1,2),(1340,(0,0))),((2,0),(1358,(0,0))),((2,2),(1370,(0,0))),((3,-1),(2024,(0,1))),((3,2),(1374,(0,0))),((4,-1),(2026,(0,1))),((4,1),(1377,(0,0))),((5,0),(1378,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_418_checked : successorFastRowCheck layer8 row7_418 row7_418choice = true := by decide
def row7_419 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1)]
def row7_419choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1741,(1,0))),((-1,2),(2248,(1,0))),((0,0),(309,(0,0))),((0,3),(1239,(0,0))),((1,0),(1312,(0,0))),((1,2),(1341,(0,0))),((2,0),(1359,(0,0))),((2,2),(1371,(0,0))),((3,-1),(2025,(0,1))),((3,2),(1375,(0,0))),((4,0),(1377,(0,0))),((4,2),(1379,(0,0))),((5,1),(1380,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_419_checked : successorFastRowCheck layer8 row7_419 row7_419choice = true := by decide
def row7_420 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1)]
def row7_420choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1742,(1,0))),((-1,2),(2249,(1,0))),((0,0),(313,(0,0))),((0,3),(1240,(0,0))),((1,0),(1316,(0,0))),((1,2),(1342,(0,0))),((2,0),(1365,(0,0))),((2,2),(1372,(0,0))),((3,0),(1377,(0,0))),((3,2),(1381,(0,0))),((4,-1),(2027,(0,1))),((4,2),(1382,(0,0))),((5,0),(1383,(0,0))),((5,1),(1384,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_420_checked : successorFastRowCheck layer8 row7_420 row7_420choice = true := by decide
def row7_421 : List GridPoint := [(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_421choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1743,(1,0))),((-1,2),(2250,(1,0))),((0,0),(329,(0,0))),((0,3),(1241,(0,0))),((1,0),(1319,(0,0))),((1,1),(1325,(0,0))),((1,4),(1386,(0,0))),((2,-1),(2028,(0,1))),((2,3),(1387,(0,0))),((3,0),(1388,(0,0))),((3,1),(1389,(0,0))),((3,2),(1390,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_421_checked : successorFastRowCheck layer8 row7_421 row7_421choice = true := by decide
def row7_422 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3)]
def row7_422choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1744,(1,0))),((-1,2),(2251,(1,0))),((0,0),(346,(0,0))),((0,3),(1242,(0,0))),((1,0),(1320,(0,0))),((1,1),(1330,(0,0))),((1,3),(1387,(0,0))),((2,-1),(2029,(0,1))),((2,4),(1393,(0,0))),((3,0),(1394,(0,0))),((3,1),(1395,(0,0))),((3,2),(1396,(0,0))),((3,3),(1397,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_422_checked : successorFastRowCheck layer8 row7_422 row7_422choice = true := by decide
def row7_423 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0)]
def row7_423choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1745,(1,0))),((-1,2),(2252,(1,0))),((0,0),(347,(0,0))),((0,3),(1243,(0,0))),((1,0),(1321,(0,0))),((1,1),(1331,(0,0))),((1,3),(1388,(0,0))),((2,-1),(2031,(0,1))),((2,3),(1394,(0,0))),((3,-1),(2034,(0,1))),((3,1),(1398,(0,0))),((3,2),(1399,(0,0))),((4,0),(1400,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_423_checked : successorFastRowCheck layer8 row7_423 row7_423choice = true := by decide
def Closure7C052rows : List (List GridPoint) := [row7_416,row7_417,row7_418,row7_419,row7_420,row7_421,row7_422,row7_423]
theorem Closure7C052_closed : ∀ row ∈ Closure7C052rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C052rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_416choice,row7_416_checked⟩
  · subst row
    exact ⟨row7_417choice,row7_417_checked⟩
  · subst row
    exact ⟨row7_418choice,row7_418_checked⟩
  · subst row
    exact ⟨row7_419choice,row7_419_checked⟩
  · subst row
    exact ⟨row7_420choice,row7_420_checked⟩
  · subst row
    exact ⟨row7_421choice,row7_421_checked⟩
  · subst row
    exact ⟨row7_422choice,row7_422_checked⟩
  · subst row
    exact ⟨row7_423choice,row7_423_checked⟩
end Polyomino57
