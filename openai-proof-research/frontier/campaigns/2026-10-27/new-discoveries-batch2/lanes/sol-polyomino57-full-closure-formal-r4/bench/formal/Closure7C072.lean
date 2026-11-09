import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_576 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row7_576choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2266,(1,0))),((-1,3),(2556,(1,0))),((0,0),(704,(0,0))),((0,1),(1180,(0,0))),((0,4),(1899,(0,0))),((1,-1),(2398,(0,1))),((1,4),(1932,(0,0))),((2,-1),(2416,(0,1))),((2,1),(1937,(0,0))),((2,2),(1938,(0,0))),((2,3),(1939,(0,0))),((3,0),(1940,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_576_checked : successorFastRowCheck layer8 row7_576 row7_576choice = true := by decide
def row7_577 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row7_577choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2267,(1,0))),((-1,3),(2557,(1,0))),((0,0),(705,(0,0))),((0,1),(1181,(0,0))),((0,4),(1900,(0,0))),((1,-1),(2399,(0,1))),((1,4),(1933,(0,0))),((2,0),(1937,(0,0))),((2,2),(1941,(0,0))),((2,3),(1942,(0,0))),((3,1),(1943,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_577_checked : successorFastRowCheck layer8 row7_577 row7_577choice = true := by decide
def row7_578 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row7_578choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2268,(1,0))),((-1,3),(2558,(1,0))),((0,0),(706,(0,0))),((0,1),(1182,(0,0))),((0,4),(1901,(0,0))),((1,-1),(2400,(0,1))),((1,4),(1934,(0,0))),((2,0),(1938,(0,0))),((2,1),(1941,(0,0))),((2,3),(1944,(0,0))),((3,2),(1945,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_578_checked : successorFastRowCheck layer8 row7_578 row7_578choice = true := by decide
def row7_579 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row7_579choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2269,(1,0))),((-1,3),(2559,(1,0))),((0,0),(707,(0,0))),((0,1),(1183,(0,0))),((0,4),(1902,(0,0))),((1,-1),(2401,(0,1))),((1,4),(1935,(0,0))),((2,0),(1939,(0,0))),((2,1),(1942,(0,0))),((2,2),(1944,(0,0))),((2,4),(1946,(0,0))),((3,3),(1947,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_579_checked : successorFastRowCheck layer8 row7_579 row7_579choice = true := by decide
def row7_580 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)]
def row7_580choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2270,(1,0))),((-1,3),(2560,(1,0))),((0,0),(708,(0,0))),((0,1),(1184,(0,0))),((0,4),(1908,(0,0))),((1,-1),(2406,(0,1))),((1,3),(1937,(0,0))),((2,-1),(2417,(0,1))),((2,2),(1948,(0,0))),((3,0),(1949,(0,0))),((3,1),(1950,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_580_checked : successorFastRowCheck layer8 row7_580 row7_580choice = true := by decide
def row7_581 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)]
def row7_581choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2271,(1,0))),((-1,3),(2561,(1,0))),((0,0),(709,(0,0))),((0,1),(1185,(0,0))),((0,4),(1909,(0,0))),((1,-1),(2407,(0,1))),((1,3),(1938,(0,0))),((2,-1),(2418,(0,1))),((2,1),(1948,(0,0))),((2,3),(1951,(0,0))),((3,0),(1952,(0,0))),((3,2),(1953,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_581_checked : successorFastRowCheck layer8 row7_581 row7_581choice = true := by decide
def row7_582 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)]
def row7_582choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2272,(1,0))),((-1,3),(2562,(1,0))),((0,0),(710,(0,0))),((0,1),(1186,(0,0))),((0,4),(1910,(0,0))),((1,-1),(2408,(0,1))),((1,3),(1940,(0,0))),((2,-1),(2420,(0,1))),((2,1),(1949,(0,0))),((2,2),(1952,(0,0))),((3,-1),(2421,(0,1))),((3,1),(1954,(0,0))),((4,0),(1955,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_582_checked : successorFastRowCheck layer8 row7_582 row7_582choice = true := by decide
def row7_583 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)]
def row7_583choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2273,(1,0))),((-1,3),(2563,(1,0))),((0,0),(711,(0,0))),((0,1),(1187,(0,0))),((0,4),(1911,(0,0))),((1,-1),(2409,(0,1))),((1,3),(1941,(0,0))),((2,0),(1948,(0,0))),((2,3),(1956,(0,0))),((3,1),(1957,(0,0))),((3,2),(1958,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_583_checked : successorFastRowCheck layer8 row7_583 row7_583choice = true := by decide
def Closure7C072rows : List (List GridPoint) := [row7_576,row7_577,row7_578,row7_579,row7_580,row7_581,row7_582,row7_583]
theorem Closure7C072_closed : ∀ row ∈ Closure7C072rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C072rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_576choice,row7_576_checked⟩
  · subst row
    exact ⟨row7_577choice,row7_577_checked⟩
  · subst row
    exact ⟨row7_578choice,row7_578_checked⟩
  · subst row
    exact ⟨row7_579choice,row7_579_checked⟩
  · subst row
    exact ⟨row7_580choice,row7_580_checked⟩
  · subst row
    exact ⟨row7_581choice,row7_581_checked⟩
  · subst row
    exact ⟨row7_582choice,row7_582_checked⟩
  · subst row
    exact ⟨row7_583choice,row7_583_checked⟩
end Polyomino57
