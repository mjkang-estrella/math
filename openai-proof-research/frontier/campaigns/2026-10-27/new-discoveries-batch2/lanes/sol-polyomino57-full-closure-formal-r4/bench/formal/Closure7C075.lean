import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_600 : List GridPoint := [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row7_600choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2290,(1,0))),((-1,3),(2580,(1,0))),((0,1),(1248,(0,0))),((0,4),(1930,(0,0))),((1,0),(1974,(0,0))),((1,1),(1995,(0,0))),((1,2),(1997,(0,0))),((1,4),(2028,(0,0))),((2,-1),(2439,(0,1))),((2,4),(2029,(0,0))),((3,0),(2030,(0,0))),((3,1),(2031,(0,0))),((3,2),(2032,(0,0))),((3,3),(2033,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_600_checked : successorFastRowCheck layer8 row7_600 row7_600choice = true := by decide
def row7_601 : List GridPoint := [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_601choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2291,(1,0))),((-1,4),(2690,(1,0))),((0,0),(716,(0,0))),((0,1),(1249,(0,0))),((0,3),(1898,(0,0))),((0,5),(2037,(0,0))),((1,-1),(2440,(0,1))),((1,5),(2038,(0,0))),((2,0),(2039,(0,0))),((2,1),(2040,(0,0))),((2,2),(2041,(0,0))),((2,3),(2042,(0,0))),((2,4),(2043,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_601_checked : successorFastRowCheck layer8 row7_601 row7_601choice = true := by decide
def row7_602 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def row7_602choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2292,(1,0))),((0,0),(717,(0,0))),((0,1),(1250,(0,0))),((0,3),(1931,(0,0))),((0,4),(2038,(0,0))),((0,5),(2046,(0,0))),((1,-1),(2441,(0,1))),((1,6),(2047,(0,0))),((2,0),(2048,(0,0))),((2,1),(2049,(0,0))),((2,2),(2050,(0,0))),((2,3),(2051,(0,0))),((2,4),(2052,(0,0))),((2,5),(2053,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_602_checked : successorFastRowCheck layer8 row7_602 row7_602choice = true := by decide
def row7_603 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def row7_603choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2293,(1,0))),((0,0),(718,(0,0))),((0,1),(1251,(0,0))),((0,3),(1932,(0,0))),((0,4),(2039,(0,0))),((1,-1),(2443,(0,1))),((1,5),(2048,(0,0))),((2,-1),(2514,(0,1))),((2,1),(2054,(0,0))),((2,2),(2055,(0,0))),((2,3),(2056,(0,0))),((2,4),(2057,(0,0))),((3,0),(2058,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_603_checked : successorFastRowCheck layer8 row7_603 row7_603choice = true := by decide
def row7_604 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def row7_604choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2294,(1,0))),((0,0),(719,(0,0))),((0,1),(1252,(0,0))),((0,3),(1933,(0,0))),((0,4),(2040,(0,0))),((1,-1),(2444,(0,1))),((1,5),(2049,(0,0))),((2,0),(2054,(0,0))),((2,2),(2059,(0,0))),((2,3),(2060,(0,0))),((2,4),(2061,(0,0))),((3,1),(2062,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_604_checked : successorFastRowCheck layer8 row7_604 row7_604choice = true := by decide
def row7_605 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def row7_605choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2295,(1,0))),((0,0),(720,(0,0))),((0,1),(1253,(0,0))),((0,3),(1934,(0,0))),((0,4),(2041,(0,0))),((1,-1),(2445,(0,1))),((1,5),(2050,(0,0))),((2,0),(2055,(0,0))),((2,1),(2059,(0,0))),((2,3),(2063,(0,0))),((2,4),(2064,(0,0))),((3,2),(2065,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_605_checked : successorFastRowCheck layer8 row7_605 row7_605choice = true := by decide
def row7_606 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def row7_606choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2296,(1,0))),((0,0),(721,(0,0))),((0,1),(1254,(0,0))),((0,3),(1935,(0,0))),((0,4),(2042,(0,0))),((1,-1),(2446,(0,1))),((1,5),(2051,(0,0))),((2,0),(2056,(0,0))),((2,1),(2060,(0,0))),((2,2),(2063,(0,0))),((2,4),(2066,(0,0))),((3,3),(2067,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_606_checked : successorFastRowCheck layer8 row7_606 row7_606choice = true := by decide
def row7_607 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def row7_607choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2297,(1,0))),((0,0),(722,(0,0))),((0,1),(1255,(0,0))),((0,3),(1936,(0,0))),((0,4),(2043,(0,0))),((1,-1),(2447,(0,1))),((1,5),(2052,(0,0))),((2,0),(2057,(0,0))),((2,1),(2061,(0,0))),((2,2),(2064,(0,0))),((2,3),(2066,(0,0))),((2,5),(2068,(0,0))),((3,4),(2069,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_607_checked : successorFastRowCheck layer8 row7_607 row7_607choice = true := by decide
def Closure7C075rows : List (List GridPoint) := [row7_600,row7_601,row7_602,row7_603,row7_604,row7_605,row7_606,row7_607]
theorem Closure7C075_closed : ∀ row ∈ Closure7C075rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C075rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_600choice,row7_600_checked⟩
  · subst row
    exact ⟨row7_601choice,row7_601_checked⟩
  · subst row
    exact ⟨row7_602choice,row7_602_checked⟩
  · subst row
    exact ⟨row7_603choice,row7_603_checked⟩
  · subst row
    exact ⟨row7_604choice,row7_604_checked⟩
  · subst row
    exact ⟨row7_605choice,row7_605_checked⟩
  · subst row
    exact ⟨row7_606choice,row7_606_checked⟩
  · subst row
    exact ⟨row7_607choice,row7_607_checked⟩
end Polyomino57
