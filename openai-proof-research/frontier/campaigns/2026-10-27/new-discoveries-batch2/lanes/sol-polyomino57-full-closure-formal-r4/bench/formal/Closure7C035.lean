import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_280 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)]
def row7_280choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1073,(1,0))),((0,-1),(576,(0,1))),((0,1),(450,(0,0))),((1,-1),(1540,(0,1))),((1,2),(851,(0,0))),((2,-1),(1703,(0,1))),((2,3),(918,(0,0))),((3,-1),(1725,(0,1))),((3,1),(922,(0,0))),((3,2),(923,(0,0))),((4,0),(924,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_280_checked : successorFastRowCheck layer8 row7_280 row7_280choice = true := by decide
def row7_281 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)]
def row7_281choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1074,(1,0))),((0,-1),(577,(0,1))),((0,1),(451,(0,0))),((1,-1),(1541,(0,1))),((1,2),(852,(0,0))),((2,-1),(1704,(0,1))),((2,3),(919,(0,0))),((3,0),(922,(0,0))),((3,2),(925,(0,0))),((4,1),(926,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_281_checked : successorFastRowCheck layer8 row7_281 row7_281choice = true := by decide
def row7_282 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]
def row7_282choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1075,(1,0))),((0,-1),(578,(0,1))),((0,1),(452,(0,0))),((1,-1),(1542,(0,1))),((1,2),(853,(0,0))),((2,-1),(1705,(0,1))),((2,3),(920,(0,0))),((3,0),(923,(0,0))),((3,1),(925,(0,0))),((3,3),(927,(0,0))),((4,2),(928,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_282_checked : successorFastRowCheck layer8 row7_282 row7_282choice = true := by decide
def row7_283 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)]
def row7_283choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1076,(1,0))),((0,-1),(580,(0,1))),((0,1),(453,(0,0))),((1,-1),(1544,(0,1))),((1,2),(854,(0,0))),((2,-1),(1709,(0,1))),((2,2),(922,(0,0))),((3,-1),(1726,(0,1))),((3,2),(929,(0,0))),((4,0),(930,(0,0))),((4,1),(931,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_283_checked : successorFastRowCheck layer8 row7_283 row7_283choice = true := by decide
def row7_284 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]
def row7_284choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1077,(1,0))),((0,-1),(581,(0,1))),((0,1),(454,(0,0))),((1,-1),(1545,(0,1))),((1,2),(855,(0,0))),((2,-1),(1710,(0,1))),((2,2),(924,(0,0))),((3,-1),(1728,(0,1))),((3,1),(930,(0,0))),((4,-1),(1729,(0,1))),((4,1),(932,(0,0))),((5,0),(933,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_284_checked : successorFastRowCheck layer8 row7_284 row7_284choice = true := by decide
def row7_285 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)]
def row7_285choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1078,(1,0))),((0,-1),(582,(0,1))),((0,1),(455,(0,0))),((1,-1),(1546,(0,1))),((1,2),(856,(0,0))),((2,-1),(1711,(0,1))),((2,2),(925,(0,0))),((3,0),(929,(0,0))),((3,3),(934,(0,0))),((4,1),(935,(0,0))),((4,2),(936,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_285_checked : successorFastRowCheck layer8 row7_285 row7_285choice = true := by decide
def row7_286 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]
def row7_286choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1079,(1,0))),((0,-1),(583,(0,1))),((0,1),(456,(0,0))),((1,-1),(1547,(0,1))),((1,2),(857,(0,0))),((2,-1),(1712,(0,1))),((2,2),(926,(0,0))),((3,0),(931,(0,0))),((3,2),(935,(0,0))),((4,0),(937,(0,0))),((4,2),(938,(0,0))),((5,1),(939,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_286_checked : successorFastRowCheck layer8 row7_286 row7_286choice = true := by decide
def row7_287 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)]
def row7_287choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1080,(1,0))),((0,-1),(587,(0,1))),((0,1),(457,(0,0))),((1,-1),(1551,(0,1))),((1,2),(868,(0,0))),((2,-1),(1718,(0,1))),((2,1),(929,(0,0))),((2,2),(940,(0,0))),((3,-1),(1730,(0,1))),((3,3),(941,(0,0))),((4,0),(942,(0,0))),((4,1),(943,(0,0))),((4,2),(944,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_287_checked : successorFastRowCheck layer8 row7_287 row7_287choice = true := by decide
def Closure7C035rows : List (List GridPoint) := [row7_280,row7_281,row7_282,row7_283,row7_284,row7_285,row7_286,row7_287]
theorem Closure7C035_closed : ∀ row ∈ Closure7C035rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C035rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_280choice,row7_280_checked⟩
  · subst row
    exact ⟨row7_281choice,row7_281_checked⟩
  · subst row
    exact ⟨row7_282choice,row7_282_checked⟩
  · subst row
    exact ⟨row7_283choice,row7_283_checked⟩
  · subst row
    exact ⟨row7_284choice,row7_284_checked⟩
  · subst row
    exact ⟨row7_285choice,row7_285_checked⟩
  · subst row
    exact ⟨row7_286choice,row7_286_checked⟩
  · subst row
    exact ⟨row7_287choice,row7_287_checked⟩
end Polyomino57
