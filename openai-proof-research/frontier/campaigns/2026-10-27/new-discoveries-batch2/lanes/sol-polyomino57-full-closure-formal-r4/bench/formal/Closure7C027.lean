import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_216 : List GridPoint := [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)]
def row7_216choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1009,(1,0))),((-1,2),(2164,(1,0))),((-1,3),(2503,(1,0))),((-1,4),(2670,(1,0))),((0,-1),(378,(0,1))),((0,1),(30,(0,0))),((0,5),(697,(0,0))),((1,-1),(1418,(0,1))),((1,3),(698,(0,0))),((1,4),(699,(0,0))),((2,0),(700,(0,0))),((2,1),(701,(0,0))),((2,2),(702,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_216_checked : successorFastRowCheck layer8 row7_216 row7_216choice = true := by decide
def row7_217 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]
def row7_217choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1010,(1,0))),((-1,2),(2165,(1,0))),((-1,3),(2504,(1,0))),((0,-1),(380,(0,1))),((0,1),(82,(0,0))),((0,4),(698,(0,0))),((1,-1),(1419,(0,1))),((1,4),(703,(0,0))),((2,0),(704,(0,0))),((2,1),(705,(0,0))),((2,2),(706,(0,0))),((2,3),(707,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_217_checked : successorFastRowCheck layer8 row7_217 row7_217choice = true := by decide
def row7_218 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)]
def row7_218choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1011,(1,0))),((-1,2),(2166,(1,0))),((-1,3),(2505,(1,0))),((0,-1),(381,(0,1))),((0,1),(83,(0,0))),((0,4),(700,(0,0))),((1,-1),(1421,(0,1))),((1,3),(704,(0,0))),((2,-1),(1424,(0,1))),((2,1),(708,(0,0))),((2,2),(709,(0,0))),((3,0),(710,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_218_checked : successorFastRowCheck layer8 row7_218 row7_218choice = true := by decide
def row7_219 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)]
def row7_219choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1012,(1,0))),((-1,2),(2167,(1,0))),((-1,3),(2506,(1,0))),((0,-1),(382,(0,1))),((0,1),(84,(0,0))),((0,4),(701,(0,0))),((1,-1),(1422,(0,1))),((1,3),(705,(0,0))),((2,0),(708,(0,0))),((2,2),(711,(0,0))),((3,1),(712,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_219_checked : successorFastRowCheck layer8 row7_219 row7_219choice = true := by decide
def row7_220 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)]
def row7_220choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1013,(1,0))),((-1,2),(2168,(1,0))),((-1,3),(2507,(1,0))),((0,-1),(383,(0,1))),((0,1),(85,(0,0))),((0,4),(702,(0,0))),((1,-1),(1423,(0,1))),((1,3),(706,(0,0))),((2,0),(709,(0,0))),((2,1),(711,(0,0))),((2,3),(713,(0,0))),((3,2),(714,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_220_checked : successorFastRowCheck layer8 row7_220 row7_220choice = true := by decide
def row7_221 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_221choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1014,(1,0))),((-1,2),(2169,(1,0))),((0,-1),(389,(0,1))),((0,1),(194,(0,0))),((0,3),(703,(0,0))),((0,4),(716,(0,0))),((1,-1),(1425,(0,1))),((1,5),(717,(0,0))),((2,0),(718,(0,0))),((2,1),(719,(0,0))),((2,2),(720,(0,0))),((2,3),(721,(0,0))),((2,4),(722,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_221_checked : successorFastRowCheck layer8 row7_221 row7_221choice = true := by decide
def row7_222 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row7_222choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1015,(1,0))),((-1,2),(2170,(1,0))),((0,-1),(390,(0,1))),((0,1),(195,(0,0))),((0,3),(704,(0,0))),((1,-1),(1427,(0,1))),((1,4),(718,(0,0))),((2,-1),(1443,(0,1))),((2,1),(723,(0,0))),((2,2),(724,(0,0))),((2,3),(725,(0,0))),((3,0),(726,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_222_checked : successorFastRowCheck layer8 row7_222 row7_222choice = true := by decide
def row7_223 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row7_223choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1016,(1,0))),((-1,2),(2171,(1,0))),((0,-1),(391,(0,1))),((0,1),(196,(0,0))),((0,3),(705,(0,0))),((1,-1),(1428,(0,1))),((1,4),(719,(0,0))),((2,0),(723,(0,0))),((2,2),(727,(0,0))),((2,3),(728,(0,0))),((3,1),(729,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_223_checked : successorFastRowCheck layer8 row7_223 row7_223choice = true := by decide
def Closure7C027rows : List (List GridPoint) := [row7_216,row7_217,row7_218,row7_219,row7_220,row7_221,row7_222,row7_223]
theorem Closure7C027_closed : ∀ row ∈ Closure7C027rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C027rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_216choice,row7_216_checked⟩
  · subst row
    exact ⟨row7_217choice,row7_217_checked⟩
  · subst row
    exact ⟨row7_218choice,row7_218_checked⟩
  · subst row
    exact ⟨row7_219choice,row7_219_checked⟩
  · subst row
    exact ⟨row7_220choice,row7_220_checked⟩
  · subst row
    exact ⟨row7_221choice,row7_221_checked⟩
  · subst row
    exact ⟨row7_222choice,row7_222_checked⟩
  · subst row
    exact ⟨row7_223choice,row7_223_checked⟩
end Polyomino57
