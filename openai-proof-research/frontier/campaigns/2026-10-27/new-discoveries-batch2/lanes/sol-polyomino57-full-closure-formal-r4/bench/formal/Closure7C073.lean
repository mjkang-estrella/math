import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_584 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)]
def row7_584choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2274,(1,0))),((-1,3),(2564,(1,0))),((0,0),(712,(0,0))),((0,1),(1188,(0,0))),((0,4),(1912,(0,0))),((1,-1),(2410,(0,1))),((1,3),(1943,(0,0))),((2,0),(1950,(0,0))),((2,2),(1957,(0,0))),((3,0),(1959,(0,0))),((3,2),(1960,(0,0))),((4,1),(1961,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_584_checked : successorFastRowCheck layer8 row7_584 row7_584choice = true := by decide
def row7_585 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)]
def row7_585choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2275,(1,0))),((-1,3),(2565,(1,0))),((0,0),(713,(0,0))),((0,1),(1189,(0,0))),((0,4),(1913,(0,0))),((1,-1),(2411,(0,1))),((1,3),(1944,(0,0))),((2,0),(1951,(0,0))),((2,1),(1956,(0,0))),((2,4),(1962,(0,0))),((3,2),(1963,(0,0))),((3,3),(1964,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_585_checked : successorFastRowCheck layer8 row7_585 row7_585choice = true := by decide
def row7_586 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)]
def row7_586choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2276,(1,0))),((-1,3),(2566,(1,0))),((0,0),(714,(0,0))),((0,1),(1190,(0,0))),((0,4),(1914,(0,0))),((1,-1),(2412,(0,1))),((1,3),(1945,(0,0))),((2,0),(1953,(0,0))),((2,1),(1958,(0,0))),((2,3),(1963,(0,0))),((3,1),(1965,(0,0))),((3,3),(1966,(0,0))),((4,2),(1967,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_586_checked : successorFastRowCheck layer8 row7_586 row7_586choice = true := by decide
def row7_587 : List GridPoint := [(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)]
def row7_587choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2277,(1,0))),((-1,3),(2567,(1,0))),((0,0),(715,(0,0))),((0,1),(1216,(0,0))),((0,4),(1915,(0,0))),((1,-1),(2413,(0,1))),((1,1),(1948,(0,0))),((1,3),(1969,(0,0))),((2,-1),(2422,(0,1))),((2,3),(1970,(0,0))),((3,0),(1971,(0,0))),((3,1),(1972,(0,0))),((3,2),(1973,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_587_checked : successorFastRowCheck layer8 row7_587 row7_587choice = true := by decide
def row7_588 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_588choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2278,(1,0))),((-1,3),(2568,(1,0))),((0,1),(1217,(0,0))),((0,4),(1916,(0,0))),((1,0),(1937,(0,0))),((1,4),(1975,(0,0))),((2,-1),(2423,(0,1))),((2,2),(1976,(0,0))),((2,3),(1977,(0,0))),((3,0),(1978,(0,0))),((3,1),(1979,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_588_checked : successorFastRowCheck layer8 row7_588 row7_588choice = true := by decide
def row7_589 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)]
def row7_589choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2279,(1,0))),((-1,3),(2569,(1,0))),((0,1),(1218,(0,0))),((0,4),(1918,(0,0))),((1,0),(1948,(0,0))),((1,3),(1976,(0,0))),((2,-1),(2424,(0,1))),((2,3),(1981,(0,0))),((3,0),(1982,(0,0))),((3,1),(1983,(0,0))),((3,2),(1984,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_589_checked : successorFastRowCheck layer8 row7_589 row7_589choice = true := by decide
def row7_590 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)]
def row7_590choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2280,(1,0))),((-1,3),(2570,(1,0))),((0,1),(1219,(0,0))),((0,4),(1919,(0,0))),((1,0),(1949,(0,0))),((1,3),(1978,(0,0))),((2,-1),(2426,(0,1))),((2,2),(1982,(0,0))),((3,-1),(2428,(0,1))),((3,1),(1985,(0,0))),((4,0),(1986,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_590_checked : successorFastRowCheck layer8 row7_590 row7_590choice = true := by decide
def row7_591 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)]
def row7_591choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2281,(1,0))),((-1,3),(2571,(1,0))),((0,1),(1220,(0,0))),((0,4),(1920,(0,0))),((1,0),(1950,(0,0))),((1,3),(1979,(0,0))),((2,-1),(2427,(0,1))),((2,2),(1983,(0,0))),((3,0),(1985,(0,0))),((3,2),(1987,(0,0))),((4,1),(1988,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_591_checked : successorFastRowCheck layer8 row7_591 row7_591choice = true := by decide
def Closure7C073rows : List (List GridPoint) := [row7_584,row7_585,row7_586,row7_587,row7_588,row7_589,row7_590,row7_591]
theorem Closure7C073_closed : ∀ row ∈ Closure7C073rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C073rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_584choice,row7_584_checked⟩
  · subst row
    exact ⟨row7_585choice,row7_585_checked⟩
  · subst row
    exact ⟨row7_586choice,row7_586_checked⟩
  · subst row
    exact ⟨row7_587choice,row7_587_checked⟩
  · subst row
    exact ⟨row7_588choice,row7_588_checked⟩
  · subst row
    exact ⟨row7_589choice,row7_589_checked⟩
  · subst row
    exact ⟨row7_590choice,row7_590_checked⟩
  · subst row
    exact ⟨row7_591choice,row7_591_checked⟩
end Polyomino57
