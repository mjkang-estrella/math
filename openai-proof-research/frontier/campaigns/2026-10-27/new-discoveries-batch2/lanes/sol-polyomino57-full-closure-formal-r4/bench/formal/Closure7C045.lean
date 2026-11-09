import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_360 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]
def row7_360choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1682,(1,0))),((-1,2),(2189,(1,0))),((-1,3),(2521,(1,0))),((0,0),(82,(0,0))),((0,4),(1154,(0,0))),((1,-1),(1898,(0,1))),((1,4),(1179,(0,0))),((2,0),(1180,(0,0))),((2,1),(1181,(0,0))),((2,2),(1182,(0,0))),((2,3),(1183,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_360_checked : successorFastRowCheck layer8 row7_360 row7_360choice = true := by decide
def row7_361 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)]
def row7_361choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1683,(1,0))),((-1,2),(2190,(1,0))),((-1,3),(2522,(1,0))),((0,0),(83,(0,0))),((0,4),(1156,(0,0))),((1,-1),(1900,(0,1))),((1,3),(1180,(0,0))),((2,-1),(1916,(0,1))),((2,1),(1184,(0,0))),((2,2),(1185,(0,0))),((3,0),(1186,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_361_checked : successorFastRowCheck layer8 row7_361 row7_361choice = true := by decide
def row7_362 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)]
def row7_362choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1684,(1,0))),((-1,2),(2191,(1,0))),((-1,3),(2523,(1,0))),((0,0),(84,(0,0))),((0,4),(1157,(0,0))),((1,-1),(1901,(0,1))),((1,3),(1181,(0,0))),((2,0),(1184,(0,0))),((2,2),(1187,(0,0))),((3,1),(1188,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_362_checked : successorFastRowCheck layer8 row7_362 row7_362choice = true := by decide
def row7_363 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)]
def row7_363choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1685,(1,0))),((-1,2),(2192,(1,0))),((-1,3),(2524,(1,0))),((0,0),(85,(0,0))),((0,4),(1158,(0,0))),((1,-1),(1902,(0,1))),((1,3),(1182,(0,0))),((2,0),(1185,(0,0))),((2,1),(1187,(0,0))),((2,3),(1189,(0,0))),((3,2),(1190,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_363_checked : successorFastRowCheck layer8 row7_363 row7_363choice = true := by decide
def row7_364 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4)]
def row7_364choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1686,(1,0))),((-1,2),(2193,(1,0))),((-1,3),(2525,(1,0))),((0,0),(86,(0,0))),((0,4),(1159,(0,0))),((1,-1),(1903,(0,1))),((1,2),(1179,(0,0))),((1,5),(1191,(0,0))),((2,0),(1192,(0,0))),((2,1),(1193,(0,0))),((2,3),(1194,(0,0))),((2,4),(1195,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_364_checked : successorFastRowCheck layer8 row7_364 row7_364choice = true := by decide
def row7_365 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0)]
def row7_365choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1687,(1,0))),((-1,2),(2194,(1,0))),((-1,3),(2526,(1,0))),((0,0),(87,(0,0))),((0,4),(1160,(0,0))),((1,-1),(1905,(0,1))),((1,2),(1180,(0,0))),((1,4),(1192,(0,0))),((2,-1),(1917,(0,1))),((2,1),(1196,(0,0))),((2,3),(1197,(0,0))),((3,0),(1198,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_365_checked : successorFastRowCheck layer8 row7_365 row7_365choice = true := by decide
def row7_366 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1)]
def row7_366choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1688,(1,0))),((-1,2),(2195,(1,0))),((-1,3),(2527,(1,0))),((0,0),(88,(0,0))),((0,4),(1161,(0,0))),((1,-1),(1906,(0,1))),((1,2),(1181,(0,0))),((1,4),(1193,(0,0))),((2,0),(1196,(0,0))),((2,2),(1199,(0,0))),((2,3),(1200,(0,0))),((3,1),(1201,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_366_checked : successorFastRowCheck layer8 row7_366 row7_366choice = true := by decide
def row7_367 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3)]
def row7_367choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1689,(1,0))),((-1,2),(2196,(1,0))),((-1,3),(2528,(1,0))),((0,0),(89,(0,0))),((0,4),(1162,(0,0))),((1,-1),(1907,(0,1))),((1,2),(1183,(0,0))),((1,4),(1194,(0,0))),((2,0),(1197,(0,0))),((2,1),(1200,(0,0))),((2,2),(1202,(0,0))),((2,4),(1203,(0,0))),((3,3),(1204,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_367_checked : successorFastRowCheck layer8 row7_367 row7_367choice = true := by decide
def Closure7C045rows : List (List GridPoint) := [row7_360,row7_361,row7_362,row7_363,row7_364,row7_365,row7_366,row7_367]
theorem Closure7C045_closed : ∀ row ∈ Closure7C045rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C045rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_360choice,row7_360_checked⟩
  · subst row
    exact ⟨row7_361choice,row7_361_checked⟩
  · subst row
    exact ⟨row7_362choice,row7_362_checked⟩
  · subst row
    exact ⟨row7_363choice,row7_363_checked⟩
  · subst row
    exact ⟨row7_364choice,row7_364_checked⟩
  · subst row
    exact ⟨row7_365choice,row7_365_checked⟩
  · subst row
    exact ⟨row7_366choice,row7_366_checked⟩
  · subst row
    exact ⟨row7_367choice,row7_367_checked⟩
end Polyomino57
