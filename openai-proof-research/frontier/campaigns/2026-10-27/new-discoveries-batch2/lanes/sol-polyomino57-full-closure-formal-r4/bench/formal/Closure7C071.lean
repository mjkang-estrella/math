import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_568 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)]
def row7_568choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2258,(1,0))),((-1,3),(2548,(1,0))),((-1,4),(2683,(1,0))),((0,0),(698,(0,0))),((0,1),(1154,(0,0))),((0,5),(1890,(0,0))),((1,-1),(2387,(0,1))),((1,4),(1898,(0,0))),((2,0),(1899,(0,0))),((2,1),(1900,(0,0))),((2,2),(1901,(0,0))),((2,3),(1902,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_568_checked : successorFastRowCheck layer8 row7_568 row7_568choice = true := by decide
def row7_569 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)]
def row7_569choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2259,(1,0))),((-1,3),(2549,(1,0))),((-1,4),(2684,(1,0))),((0,0),(699,(0,0))),((0,1),(1155,(0,0))),((0,5),(1891,(0,0))),((1,-1),(2388,(0,1))),((1,3),(1898,(0,0))),((1,5),(1903,(0,0))),((2,0),(1904,(0,0))),((2,1),(1905,(0,0))),((2,2),(1906,(0,0))),((2,4),(1907,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_569_checked : successorFastRowCheck layer8 row7_569 row7_569choice = true := by decide
def row7_570 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)]
def row7_570choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2260,(1,0))),((-1,3),(2550,(1,0))),((-1,4),(2685,(1,0))),((0,0),(700,(0,0))),((0,1),(1156,(0,0))),((0,5),(1893,(0,0))),((1,-1),(2390,(0,1))),((1,3),(1899,(0,0))),((1,4),(1904,(0,0))),((2,-1),(2393,(0,1))),((2,1),(1908,(0,0))),((2,2),(1909,(0,0))),((3,0),(1910,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_570_checked : successorFastRowCheck layer8 row7_570 row7_570choice = true := by decide
def row7_571 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)]
def row7_571choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2261,(1,0))),((-1,3),(2551,(1,0))),((-1,4),(2686,(1,0))),((0,0),(701,(0,0))),((0,1),(1157,(0,0))),((0,5),(1894,(0,0))),((1,-1),(2391,(0,1))),((1,3),(1900,(0,0))),((1,4),(1905,(0,0))),((2,0),(1908,(0,0))),((2,2),(1911,(0,0))),((3,1),(1912,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_571_checked : successorFastRowCheck layer8 row7_571 row7_571choice = true := by decide
def row7_572 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)]
def row7_572choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2262,(1,0))),((-1,3),(2552,(1,0))),((-1,4),(2687,(1,0))),((0,0),(702,(0,0))),((0,1),(1158,(0,0))),((0,5),(1895,(0,0))),((1,-1),(2392,(0,1))),((1,3),(1901,(0,0))),((1,4),(1906,(0,0))),((2,0),(1909,(0,0))),((2,1),(1911,(0,0))),((2,3),(1913,(0,0))),((3,2),(1914,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_572_checked : successorFastRowCheck layer8 row7_572 row7_572choice = true := by decide
def row7_573 : List GridPoint := [(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)]
def row7_573choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2263,(1,0))),((-1,3),(2553,(1,0))),((-1,4),(2688,(1,0))),((0,1),(1171,(0,0))),((0,5),(1896,(0,0))),((1,0),(1908,(0,0))),((1,3),(1916,(0,0))),((1,4),(1917,(0,0))),((2,-1),(2394,(0,1))),((2,2),(1918,(0,0))),((3,0),(1919,(0,0))),((3,1),(1920,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_573_checked : successorFastRowCheck layer8 row7_573 row7_573choice = true := by decide
def row7_574 : List GridPoint := [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)]
def row7_574choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2264,(1,0))),((-1,3),(2554,(1,0))),((-1,4),(2689,(1,0))),((0,1),(1178,(0,0))),((0,5),(1897,(0,0))),((1,0),(1915,(0,0))),((1,1),(1918,(0,0))),((1,3),(1922,(0,0))),((1,4),(1923,(0,0))),((2,-1),(2395,(0,1))),((2,3),(1924,(0,0))),((3,0),(1925,(0,0))),((3,1),(1926,(0,0))),((3,2),(1927,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_574_checked : successorFastRowCheck layer8 row7_574 row7_574choice = true := by decide
def row7_575 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_575choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2265,(1,0))),((-1,3),(2555,(1,0))),((0,0),(703,(0,0))),((0,1),(1179,(0,0))),((0,4),(1898,(0,0))),((1,-1),(2396,(0,1))),((1,5),(1931,(0,0))),((2,0),(1932,(0,0))),((2,1),(1933,(0,0))),((2,2),(1934,(0,0))),((2,3),(1935,(0,0))),((2,4),(1936,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_575_checked : successorFastRowCheck layer8 row7_575 row7_575choice = true := by decide
def Closure7C071rows : List (List GridPoint) := [row7_568,row7_569,row7_570,row7_571,row7_572,row7_573,row7_574,row7_575]
theorem Closure7C071_closed : ∀ row ∈ Closure7C071rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C071rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_568choice,row7_568_checked⟩
  · subst row
    exact ⟨row7_569choice,row7_569_checked⟩
  · subst row
    exact ⟨row7_570choice,row7_570_checked⟩
  · subst row
    exact ⟨row7_571choice,row7_571_checked⟩
  · subst row
    exact ⟨row7_572choice,row7_572_checked⟩
  · subst row
    exact ⟨row7_573choice,row7_573_checked⟩
  · subst row
    exact ⟨row7_574choice,row7_574_checked⟩
  · subst row
    exact ⟨row7_575choice,row7_575_checked⟩
end Polyomino57
