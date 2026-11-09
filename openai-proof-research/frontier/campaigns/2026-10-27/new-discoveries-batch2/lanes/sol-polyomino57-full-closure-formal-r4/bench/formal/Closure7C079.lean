import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_632 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]
def row7_632choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2322,(1,0))),((0,0),(747,(0,0))),((0,1),(1280,(0,0))),((0,3),(1961,(0,0))),((1,-1),(2490,(0,1))),((1,3),(2090,(0,0))),((2,0),(2111,(0,0))),((2,2),(2133,(0,0))),((3,0),(2138,(0,0))),((3,2),(2140,(0,0))),((4,0),(2142,(0,0))),((4,2),(2143,(0,0))),((5,1),(2144,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_632_checked : successorFastRowCheck layer8 row7_632 row7_632choice = true := by decide
def row7_633 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)]
def row7_633choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2323,(1,0))),((0,0),(748,(0,0))),((0,1),(1281,(0,0))),((0,3),(1962,(0,0))),((1,-1),(2491,(0,1))),((1,3),(2091,(0,0))),((1,4),(2103,(0,0))),((2,0),(2112,(0,0))),((2,1),(2127,(0,0))),((2,5),(2145,(0,0))),((3,2),(2146,(0,0))),((3,3),(2147,(0,0))),((3,4),(2148,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_633_checked : successorFastRowCheck layer8 row7_633 row7_633choice = true := by decide
def row7_634 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)]
def row7_634choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2324,(1,0))),((0,0),(749,(0,0))),((0,1),(1282,(0,0))),((0,3),(1963,(0,0))),((1,-1),(2492,(0,1))),((1,3),(2092,(0,0))),((2,0),(2114,(0,0))),((2,1),(2129,(0,0))),((2,4),(2146,(0,0))),((3,1),(2149,(0,0))),((3,3),(2150,(0,0))),((4,2),(2151,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_634_checked : successorFastRowCheck layer8 row7_634 row7_634choice = true := by decide
def row7_635 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]
def row7_635choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2325,(1,0))),((0,0),(750,(0,0))),((0,1),(1283,(0,0))),((0,3),(1964,(0,0))),((1,-1),(2493,(0,1))),((1,3),(2093,(0,0))),((2,0),(2115,(0,0))),((2,1),(2130,(0,0))),((2,4),(2147,(0,0))),((3,2),(2150,(0,0))),((3,4),(2152,(0,0))),((4,3),(2153,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_635_checked : successorFastRowCheck layer8 row7_635 row7_635choice = true := by decide
def row7_636 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)]
def row7_636choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2326,(1,0))),((0,0),(751,(0,0))),((0,1),(1284,(0,0))),((0,3),(1965,(0,0))),((1,-1),(2494,(0,1))),((1,3),(2094,(0,0))),((2,0),(2119,(0,0))),((2,1),(2132,(0,0))),((2,3),(2149,(0,0))),((3,0),(2154,(0,0))),((3,3),(2155,(0,0))),((4,1),(2156,(0,0))),((4,2),(2157,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_636_checked : successorFastRowCheck layer8 row7_636 row7_636choice = true := by decide
def row7_637 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)]
def row7_637choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2327,(1,0))),((0,0),(752,(0,0))),((0,1),(1285,(0,0))),((0,3),(1966,(0,0))),((1,-1),(2495,(0,1))),((1,3),(2095,(0,0))),((2,0),(2120,(0,0))),((2,1),(2134,(0,0))),((2,3),(2150,(0,0))),((3,1),(2155,(0,0))),((3,4),(2158,(0,0))),((4,2),(2159,(0,0))),((4,3),(2160,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_637_checked : successorFastRowCheck layer8 row7_637 row7_637choice = true := by decide
def row7_638 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]
def row7_638choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2328,(1,0))),((0,0),(753,(0,0))),((0,1),(1286,(0,0))),((0,3),(1967,(0,0))),((1,-1),(2496,(0,1))),((1,3),(2096,(0,0))),((2,0),(2121,(0,0))),((2,1),(2135,(0,0))),((2,3),(2151,(0,0))),((3,1),(2157,(0,0))),((3,3),(2159,(0,0))),((4,1),(2161,(0,0))),((4,3),(2162,(0,0))),((5,2),(2163,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_638_checked : successorFastRowCheck layer8 row7_638 row7_638choice = true := by decide
def row7_639 : List GridPoint := [(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_639choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2329,(1,0))),((0,0),(754,(0,0))),((0,1),(1319,(0,0))),((0,3),(1969,(0,0))),((1,-1),(2497,(0,1))),((1,1),(2070,(0,0))),((1,4),(2164,(0,0))),((2,-1),(2540,(0,1))),((2,3),(2165,(0,0))),((3,0),(2166,(0,0))),((3,1),(2167,(0,0))),((3,2),(2168,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_639_checked : successorFastRowCheck layer8 row7_639 row7_639choice = true := by decide
def Closure7C079rows : List (List GridPoint) := [row7_632,row7_633,row7_634,row7_635,row7_636,row7_637,row7_638,row7_639]
theorem Closure7C079_closed : ∀ row ∈ Closure7C079rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C079rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_632choice,row7_632_checked⟩
  · subst row
    exact ⟨row7_633choice,row7_633_checked⟩
  · subst row
    exact ⟨row7_634choice,row7_634_checked⟩
  · subst row
    exact ⟨row7_635choice,row7_635_checked⟩
  · subst row
    exact ⟨row7_636choice,row7_636_checked⟩
  · subst row
    exact ⟨row7_637choice,row7_637_checked⟩
  · subst row
    exact ⟨row7_638choice,row7_638_checked⟩
  · subst row
    exact ⟨row7_639choice,row7_639_checked⟩
end Polyomino57
