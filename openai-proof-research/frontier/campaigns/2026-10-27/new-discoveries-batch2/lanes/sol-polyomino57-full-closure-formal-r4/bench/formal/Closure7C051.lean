import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_408 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3)]
def row7_408choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1730,(1,0))),((-1,2),(2237,(1,0))),((0,0),(290,(0,0))),((0,3),(1228,(0,0))),((1,0),(1288,(0,0))),((1,2),(1330,(0,0))),((1,3),(1344,(0,0))),((2,-1),(2003,(0,1))),((2,4),(1345,(0,0))),((3,0),(1346,(0,0))),((3,1),(1347,(0,0))),((3,2),(1348,(0,0))),((3,3),(1349,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_408_checked : successorFastRowCheck layer8 row7_408 row7_408choice = true := by decide
def row7_409 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0)]
def row7_409choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1731,(1,0))),((-1,2),(2238,(1,0))),((0,0),(291,(0,0))),((0,3),(1229,(0,0))),((1,0),(1289,(0,0))),((1,2),(1331,(0,0))),((2,-1),(2005,(0,1))),((2,3),(1346,(0,0))),((3,-1),(2016,(0,1))),((3,1),(1350,(0,0))),((3,2),(1351,(0,0))),((4,0),(1352,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_409_checked : successorFastRowCheck layer8 row7_409 row7_409choice = true := by decide
def row7_410 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)]
def row7_410choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1732,(1,0))),((-1,2),(2239,(1,0))),((0,0),(292,(0,0))),((0,3),(1230,(0,0))),((1,0),(1290,(0,0))),((1,2),(1332,(0,0))),((2,-1),(2006,(0,1))),((2,3),(1347,(0,0))),((3,0),(1350,(0,0))),((3,2),(1353,(0,0))),((4,1),(1354,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_410_checked : successorFastRowCheck layer8 row7_410 row7_410choice = true := by decide
def row7_411 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2)]
def row7_411choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1733,(1,0))),((-1,2),(2240,(1,0))),((0,0),(293,(0,0))),((0,3),(1231,(0,0))),((1,0),(1291,(0,0))),((1,2),(1333,(0,0))),((2,-1),(2007,(0,1))),((2,3),(1348,(0,0))),((3,0),(1351,(0,0))),((3,1),(1353,(0,0))),((3,3),(1355,(0,0))),((4,2),(1356,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_411_checked : successorFastRowCheck layer8 row7_411 row7_411choice = true := by decide
def row7_412 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)]
def row7_412choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1734,(1,0))),((-1,2),(2241,(1,0))),((0,0),(294,(0,0))),((0,3),(1232,(0,0))),((1,0),(1292,(0,0))),((1,2),(1334,(0,0))),((2,-1),(2011,(0,1))),((2,2),(1350,(0,0))),((3,-1),(2017,(0,1))),((3,2),(1357,(0,0))),((4,0),(1358,(0,0))),((4,1),(1359,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_412_checked : successorFastRowCheck layer8 row7_412 row7_412choice = true := by decide
def row7_413 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0)]
def row7_413choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1735,(1,0))),((-1,2),(2242,(1,0))),((0,0),(295,(0,0))),((0,3),(1233,(0,0))),((1,0),(1293,(0,0))),((1,2),(1335,(0,0))),((2,-1),(2012,(0,1))),((2,2),(1352,(0,0))),((3,-1),(2019,(0,1))),((3,1),(1358,(0,0))),((4,-1),(2020,(0,1))),((4,1),(1360,(0,0))),((5,0),(1361,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_413_checked : successorFastRowCheck layer8 row7_413 row7_413choice = true := by decide
def row7_414 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2)]
def row7_414choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1736,(1,0))),((-1,2),(2243,(1,0))),((0,0),(296,(0,0))),((0,3),(1234,(0,0))),((1,0),(1294,(0,0))),((1,2),(1336,(0,0))),((2,-1),(2013,(0,1))),((2,2),(1353,(0,0))),((3,0),(1357,(0,0))),((3,3),(1362,(0,0))),((4,1),(1363,(0,0))),((4,2),(1364,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_414_checked : successorFastRowCheck layer8 row7_414 row7_414choice = true := by decide
def row7_415 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1)]
def row7_415choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1737,(1,0))),((-1,2),(2244,(1,0))),((0,0),(297,(0,0))),((0,3),(1235,(0,0))),((1,0),(1295,(0,0))),((1,2),(1337,(0,0))),((2,-1),(2014,(0,1))),((2,2),(1354,(0,0))),((3,0),(1359,(0,0))),((3,2),(1363,(0,0))),((4,0),(1365,(0,0))),((4,2),(1366,(0,0))),((5,1),(1367,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_415_checked : successorFastRowCheck layer8 row7_415 row7_415choice = true := by decide
def Closure7C051rows : List (List GridPoint) := [row7_408,row7_409,row7_410,row7_411,row7_412,row7_413,row7_414,row7_415]
theorem Closure7C051_closed : ∀ row ∈ Closure7C051rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C051rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_408choice,row7_408_checked⟩
  · subst row
    exact ⟨row7_409choice,row7_409_checked⟩
  · subst row
    exact ⟨row7_410choice,row7_410_checked⟩
  · subst row
    exact ⟨row7_411choice,row7_411_checked⟩
  · subst row
    exact ⟨row7_412choice,row7_412_checked⟩
  · subst row
    exact ⟨row7_413choice,row7_413_checked⟩
  · subst row
    exact ⟨row7_414choice,row7_414_checked⟩
  · subst row
    exact ⟨row7_415choice,row7_415_checked⟩
end Polyomino57
