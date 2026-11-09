import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_312 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)]
def row7_312choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1105,(1,0))),((0,-1),(615,(0,1))),((0,1),(482,(0,0))),((0,2),(756,(0,0))),((1,-1),(1579,(0,1))),((1,1),(851,(0,0))),((1,3),(1011,(0,0))),((2,-1),(1753,(0,1))),((2,3),(1015,(0,0))),((3,-1),(1756,(0,1))),((3,1),(1019,(0,0))),((3,2),(1020,(0,0))),((4,0),(1021,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_312_checked : successorFastRowCheck layer8 row7_312 row7_312choice = true := by decide
def row7_313 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)]
def row7_313choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1106,(1,0))),((0,-1),(616,(0,1))),((0,1),(483,(0,0))),((0,2),(757,(0,0))),((1,-1),(1580,(0,1))),((1,1),(852,(0,0))),((1,3),(1012,(0,0))),((2,-1),(1754,(0,1))),((2,3),(1016,(0,0))),((3,0),(1019,(0,0))),((3,2),(1022,(0,0))),((4,1),(1023,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_313_checked : successorFastRowCheck layer8 row7_313 row7_313choice = true := by decide
def row7_314 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]
def row7_314choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1107,(1,0))),((0,-1),(617,(0,1))),((0,1),(484,(0,0))),((0,2),(758,(0,0))),((1,-1),(1581,(0,1))),((1,1),(853,(0,0))),((1,3),(1013,(0,0))),((2,-1),(1755,(0,1))),((2,3),(1017,(0,0))),((3,0),(1020,(0,0))),((3,1),(1022,(0,0))),((3,3),(1024,(0,0))),((4,2),(1025,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_314_checked : successorFastRowCheck layer8 row7_314 row7_314choice = true := by decide
def row7_315 : List GridPoint := [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row7_315choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1108,(1,0))),((0,-1),(618,(0,1))),((0,1),(485,(0,0))),((0,3),(784,(0,0))),((1,-1),(1582,(0,1))),((1,1),(911,(0,0))),((1,2),(1010,(0,0))),((1,4),(1027,(0,0))),((2,-1),(1757,(0,1))),((2,4),(1028,(0,0))),((3,0),(1029,(0,0))),((3,1),(1030,(0,0))),((3,2),(1031,(0,0))),((3,3),(1032,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_315_checked : successorFastRowCheck layer8 row7_315 row7_315choice = true := by decide
def row7_316 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)]
def row7_316choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1109,(1,0))),((0,-1),(642,(0,1))),((0,1),(486,(0,0))),((1,-1),(1620,(0,1))),((1,1),(917,(0,0))),((1,2),(1014,(0,0))),((1,3),(1028,(0,0))),((1,4),(1033,(0,0))),((2,-1),(1758,(0,1))),((2,5),(1034,(0,0))),((3,0),(1035,(0,0))),((3,1),(1036,(0,0))),((3,2),(1037,(0,0))),((3,3),(1038,(0,0))),((3,4),(1039,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_316_checked : successorFastRowCheck layer8 row7_316 row7_316choice = true := by decide
def row7_317 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)]
def row7_317choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1110,(1,0))),((0,-1),(643,(0,1))),((0,1),(487,(0,0))),((1,-1),(1621,(0,1))),((1,1),(918,(0,0))),((1,2),(1015,(0,0))),((1,3),(1029,(0,0))),((2,-1),(1760,(0,1))),((2,4),(1035,(0,0))),((3,-1),(1827,(0,1))),((3,1),(1040,(0,0))),((3,2),(1041,(0,0))),((3,3),(1042,(0,0))),((4,0),(1043,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_317_checked : successorFastRowCheck layer8 row7_317 row7_317choice = true := by decide
def row7_318 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)]
def row7_318choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1111,(1,0))),((0,-1),(644,(0,1))),((0,1),(488,(0,0))),((1,-1),(1622,(0,1))),((1,1),(919,(0,0))),((1,2),(1016,(0,0))),((1,3),(1030,(0,0))),((2,-1),(1761,(0,1))),((2,4),(1036,(0,0))),((3,0),(1040,(0,0))),((3,2),(1044,(0,0))),((3,3),(1045,(0,0))),((4,1),(1046,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_318_checked : successorFastRowCheck layer8 row7_318 row7_318choice = true := by decide
def row7_319 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)]
def row7_319choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1112,(1,0))),((0,-1),(645,(0,1))),((0,1),(489,(0,0))),((1,-1),(1623,(0,1))),((1,1),(920,(0,0))),((1,2),(1017,(0,0))),((1,3),(1031,(0,0))),((2,-1),(1762,(0,1))),((2,4),(1037,(0,0))),((3,0),(1041,(0,0))),((3,1),(1044,(0,0))),((3,3),(1047,(0,0))),((4,2),(1048,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_319_checked : successorFastRowCheck layer8 row7_319 row7_319choice = true := by decide
def Closure7C039rows : List (List GridPoint) := [row7_312,row7_313,row7_314,row7_315,row7_316,row7_317,row7_318,row7_319]
theorem Closure7C039_closed : ∀ row ∈ Closure7C039rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C039rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_312choice,row7_312_checked⟩
  · subst row
    exact ⟨row7_313choice,row7_313_checked⟩
  · subst row
    exact ⟨row7_314choice,row7_314_checked⟩
  · subst row
    exact ⟨row7_315choice,row7_315_checked⟩
  · subst row
    exact ⟨row7_316choice,row7_316_checked⟩
  · subst row
    exact ⟨row7_317choice,row7_317_checked⟩
  · subst row
    exact ⟨row7_318choice,row7_318_checked⟩
  · subst row
    exact ⟨row7_319choice,row7_319_checked⟩
end Polyomino57
