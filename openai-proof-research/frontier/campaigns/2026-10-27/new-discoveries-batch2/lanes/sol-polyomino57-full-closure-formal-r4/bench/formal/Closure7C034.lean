import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_272 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)]
def row7_272choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1065,(1,0))),((0,-1),(560,(0,1))),((0,1),(442,(0,0))),((0,2),(748,(0,0))),((1,-1),(1509,(0,1))),((1,3),(837,(0,0))),((1,4),(849,(0,0))),((2,0),(858,(0,0))),((2,1),(873,(0,0))),((2,5),(891,(0,0))),((3,2),(892,(0,0))),((3,3),(893,(0,0))),((3,4),(894,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_272_checked : successorFastRowCheck layer8 row7_272 row7_272choice = true := by decide
def row7_273 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)]
def row7_273choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1066,(1,0))),((0,-1),(561,(0,1))),((0,1),(443,(0,0))),((0,2),(749,(0,0))),((1,-1),(1510,(0,1))),((1,3),(838,(0,0))),((2,0),(860,(0,0))),((2,1),(875,(0,0))),((2,4),(892,(0,0))),((3,1),(895,(0,0))),((3,3),(896,(0,0))),((4,2),(897,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_273_checked : successorFastRowCheck layer8 row7_273 row7_273choice = true := by decide
def row7_274 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]
def row7_274choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1067,(1,0))),((0,-1),(562,(0,1))),((0,1),(444,(0,0))),((0,2),(750,(0,0))),((1,-1),(1511,(0,1))),((1,3),(839,(0,0))),((2,0),(861,(0,0))),((2,1),(876,(0,0))),((2,4),(893,(0,0))),((3,2),(896,(0,0))),((3,4),(898,(0,0))),((4,3),(899,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_274_checked : successorFastRowCheck layer8 row7_274 row7_274choice = true := by decide
def row7_275 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)]
def row7_275choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1068,(1,0))),((0,-1),(563,(0,1))),((0,1),(445,(0,0))),((0,2),(751,(0,0))),((1,-1),(1512,(0,1))),((1,3),(840,(0,0))),((2,0),(865,(0,0))),((2,1),(878,(0,0))),((2,3),(895,(0,0))),((3,0),(900,(0,0))),((3,3),(901,(0,0))),((4,1),(902,(0,0))),((4,2),(903,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_275_checked : successorFastRowCheck layer8 row7_275 row7_275choice = true := by decide
def row7_276 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)]
def row7_276choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1069,(1,0))),((0,-1),(564,(0,1))),((0,1),(446,(0,0))),((0,2),(752,(0,0))),((1,-1),(1513,(0,1))),((1,3),(841,(0,0))),((2,0),(866,(0,0))),((2,1),(880,(0,0))),((2,3),(896,(0,0))),((3,1),(901,(0,0))),((3,4),(904,(0,0))),((4,2),(905,(0,0))),((4,3),(906,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_276_checked : successorFastRowCheck layer8 row7_276 row7_276choice = true := by decide
def row7_277 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]
def row7_277choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1070,(1,0))),((0,-1),(565,(0,1))),((0,1),(447,(0,0))),((0,2),(753,(0,0))),((1,-1),(1514,(0,1))),((1,3),(842,(0,0))),((2,0),(867,(0,0))),((2,1),(881,(0,0))),((2,3),(897,(0,0))),((3,1),(903,(0,0))),((3,3),(905,(0,0))),((4,1),(907,(0,0))),((4,3),(908,(0,0))),((5,2),(909,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_277_checked : successorFastRowCheck layer8 row7_277 row7_277choice = true := by decide
def row7_278 : List GridPoint := [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)]
def row7_278choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1071,(1,0))),((0,-1),(566,(0,1))),((0,1),(448,(0,0))),((0,3),(782,(0,0))),((1,-1),(1515,(0,1))),((1,2),(828,(0,0))),((1,4),(910,(0,0))),((2,0),(911,(0,0))),((2,4),(912,(0,0))),((3,1),(913,(0,0))),((3,2),(914,(0,0))),((3,3),(915,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_278_checked : successorFastRowCheck layer8 row7_278 row7_278choice = true := by decide
def row7_279 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)]
def row7_279choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1072,(1,0))),((0,-1),(575,(0,1))),((0,1),(449,(0,0))),((1,-1),(1539,(0,1))),((1,2),(850,(0,0))),((1,3),(911,(0,0))),((2,-1),(1701,(0,1))),((2,4),(917,(0,0))),((3,0),(918,(0,0))),((3,1),(919,(0,0))),((3,2),(920,(0,0))),((3,3),(921,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_279_checked : successorFastRowCheck layer8 row7_279 row7_279choice = true := by decide
def Closure7C034rows : List (List GridPoint) := [row7_272,row7_273,row7_274,row7_275,row7_276,row7_277,row7_278,row7_279]
theorem Closure7C034_closed : ∀ row ∈ Closure7C034rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C034rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_272choice,row7_272_checked⟩
  · subst row
    exact ⟨row7_273choice,row7_273_checked⟩
  · subst row
    exact ⟨row7_274choice,row7_274_checked⟩
  · subst row
    exact ⟨row7_275choice,row7_275_checked⟩
  · subst row
    exact ⟨row7_276choice,row7_276_checked⟩
  · subst row
    exact ⟨row7_277choice,row7_277_checked⟩
  · subst row
    exact ⟨row7_278choice,row7_278_checked⟩
  · subst row
    exact ⟨row7_279choice,row7_279_checked⟩
end Polyomino57
