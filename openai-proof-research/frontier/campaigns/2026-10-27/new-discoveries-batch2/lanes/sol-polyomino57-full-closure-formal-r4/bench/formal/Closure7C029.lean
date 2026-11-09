import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_232 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)]
def row7_232choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1025,(1,0))),((-1,2),(2180,(1,0))),((0,-1),(401,(0,1))),((0,1),(205,(0,0))),((0,3),(714,(0,0))),((1,-1),(1441,(0,1))),((1,3),(731,(0,0))),((2,0),(739,(0,0))),((2,1),(744,(0,0))),((2,3),(749,(0,0))),((3,1),(751,(0,0))),((3,3),(752,(0,0))),((4,2),(753,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_232_checked : successorFastRowCheck layer8 row7_232 row7_232choice = true := by decide
def row7_233 : List GridPoint := [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)]
def row7_233choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1026,(1,0))),((-1,2),(2181,(1,0))),((0,-1),(402,(0,1))),((0,1),(231,(0,0))),((0,3),(715,(0,0))),((1,-1),(1442,(0,1))),((1,1),(734,(0,0))),((1,3),(754,(0,0))),((2,-1),(1449,(0,1))),((2,3),(755,(0,0))),((3,0),(756,(0,0))),((3,1),(757,(0,0))),((3,2),(758,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_233_checked : successorFastRowCheck layer8 row7_233 row7_233choice = true := by decide
def row7_234 : List GridPoint := [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)]
def row7_234choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1027,(1,0))),((-1,3),(2508,(1,0))),((-1,4),(2671,(1,0))),((0,-1),(403,(0,1))),((0,1),(379,(0,0))),((0,2),(698,(0,0))),((0,5),(759,(0,0))),((1,-1),(1450,(0,1))),((1,4),(760,(0,0))),((2,0),(761,(0,0))),((2,1),(762,(0,0))),((2,2),(763,(0,0))),((2,3),(764,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_234_checked : successorFastRowCheck layer8 row7_234 row7_234choice = true := by decide
def row7_235 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_235choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1028,(1,0))),((-1,3),(2509,(1,0))),((0,-1),(405,(0,1))),((0,1),(384,(0,0))),((0,2),(703,(0,0))),((0,4),(760,(0,0))),((1,-1),(1451,(0,1))),((1,5),(765,(0,0))),((2,0),(766,(0,0))),((2,1),(767,(0,0))),((2,2),(768,(0,0))),((2,3),(769,(0,0))),((2,4),(770,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_235_checked : successorFastRowCheck layer8 row7_235 row7_235choice = true := by decide
def row7_236 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row7_236choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1029,(1,0))),((-1,3),(2510,(1,0))),((0,-1),(406,(0,1))),((0,1),(385,(0,0))),((0,2),(704,(0,0))),((0,4),(761,(0,0))),((1,-1),(1453,(0,1))),((1,4),(766,(0,0))),((2,-1),(1457,(0,1))),((2,1),(771,(0,0))),((2,2),(772,(0,0))),((2,3),(773,(0,0))),((3,0),(774,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_236_checked : successorFastRowCheck layer8 row7_236 row7_236choice = true := by decide
def row7_237 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row7_237choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1030,(1,0))),((-1,3),(2511,(1,0))),((0,-1),(407,(0,1))),((0,1),(386,(0,0))),((0,2),(705,(0,0))),((0,4),(762,(0,0))),((1,-1),(1454,(0,1))),((1,4),(767,(0,0))),((2,0),(771,(0,0))),((2,2),(775,(0,0))),((2,3),(776,(0,0))),((3,1),(777,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_237_checked : successorFastRowCheck layer8 row7_237 row7_237choice = true := by decide
def row7_238 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row7_238choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1031,(1,0))),((-1,3),(2512,(1,0))),((0,-1),(408,(0,1))),((0,1),(387,(0,0))),((0,2),(706,(0,0))),((0,4),(763,(0,0))),((1,-1),(1455,(0,1))),((1,4),(768,(0,0))),((2,0),(772,(0,0))),((2,1),(775,(0,0))),((2,3),(778,(0,0))),((3,2),(779,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_238_checked : successorFastRowCheck layer8 row7_238 row7_238choice = true := by decide
def row7_239 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row7_239choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1032,(1,0))),((-1,3),(2513,(1,0))),((0,-1),(409,(0,1))),((0,1),(388,(0,0))),((0,2),(707,(0,0))),((0,4),(764,(0,0))),((1,-1),(1456,(0,1))),((1,4),(769,(0,0))),((2,0),(773,(0,0))),((2,1),(776,(0,0))),((2,2),(778,(0,0))),((2,4),(780,(0,0))),((3,3),(781,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_239_checked : successorFastRowCheck layer8 row7_239 row7_239choice = true := by decide
def Closure7C029rows : List (List GridPoint) := [row7_232,row7_233,row7_234,row7_235,row7_236,row7_237,row7_238,row7_239]
theorem Closure7C029_closed : ∀ row ∈ Closure7C029rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C029rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_232choice,row7_232_checked⟩
  · subst row
    exact ⟨row7_233choice,row7_233_checked⟩
  · subst row
    exact ⟨row7_234choice,row7_234_checked⟩
  · subst row
    exact ⟨row7_235choice,row7_235_checked⟩
  · subst row
    exact ⟨row7_236choice,row7_236_checked⟩
  · subst row
    exact ⟨row7_237choice,row7_237_checked⟩
  · subst row
    exact ⟨row7_238choice,row7_238_checked⟩
  · subst row
    exact ⟨row7_239choice,row7_239_checked⟩
end Polyomino57
