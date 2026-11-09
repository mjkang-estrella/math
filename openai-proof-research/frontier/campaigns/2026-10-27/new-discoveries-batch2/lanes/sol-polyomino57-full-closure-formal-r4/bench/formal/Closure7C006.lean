import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_48 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3)]
def row7_48choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(841,(1,0))),((-1,1),(1507,(1,0))),((-1,2),(2095,(1,0))),((-1,3),(2489,(1,0))),((0,-1),(73,(0,1))),((0,4),(67,(0,0))),((1,0),(102,(0,0))),((1,1),(126,(0,0))),((1,3),(153,(0,0))),((2,1),(158,(0,0))),((2,4),(161,(0,0))),((3,2),(162,(0,0))),((3,3),(163,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_48_checked : successorFastRowCheck layer8 row7_48 row7_48choice = true := by decide
def row7_49 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2)]
def row7_49choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(842,(1,0))),((-1,1),(1508,(1,0))),((-1,2),(2096,(1,0))),((-1,3),(2490,(1,0))),((0,-1),(74,(0,1))),((0,4),(68,(0,0))),((1,0),(103,(0,0))),((1,1),(127,(0,0))),((1,3),(154,(0,0))),((2,1),(160,(0,0))),((2,3),(162,(0,0))),((3,1),(164,(0,0))),((3,3),(165,(0,0))),((4,2),(166,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_49_checked : successorFastRowCheck layer8 row7_49 row7_49choice = true := by decide
def row7_50 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5)]
def row7_50choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(843,(1,0))),((-1,1),(1509,(1,0))),((-1,2),(2097,(1,0))),((-1,3),(2491,(1,0))),((0,-1),(75,(0,1))),((0,4),(69,(0,0))),((0,5),(81,(0,0))),((1,0),(104,(0,0))),((1,1),(128,(0,0))),((1,2),(148,(0,0))),((1,6),(167,(0,0))),((2,3),(168,(0,0))),((2,4),(169,(0,0))),((2,5),(170,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_50_checked : successorFastRowCheck layer8 row7_50 row7_50choice = true := by decide
def row7_51 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3)]
def row7_51choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(844,(1,0))),((-1,1),(1510,(1,0))),((-1,2),(2098,(1,0))),((-1,3),(2492,(1,0))),((0,-1),(76,(0,1))),((0,4),(70,(0,0))),((1,0),(106,(0,0))),((1,1),(130,(0,0))),((1,2),(150,(0,0))),((1,5),(168,(0,0))),((2,2),(171,(0,0))),((2,4),(172,(0,0))),((3,3),(173,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_51_checked : successorFastRowCheck layer8 row7_51 row7_51choice = true := by decide
def row7_52 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4)]
def row7_52choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(845,(1,0))),((-1,1),(1511,(1,0))),((-1,2),(2099,(1,0))),((-1,3),(2493,(1,0))),((0,-1),(77,(0,1))),((0,4),(71,(0,0))),((1,0),(107,(0,0))),((1,1),(131,(0,0))),((1,2),(151,(0,0))),((1,5),(169,(0,0))),((2,3),(172,(0,0))),((2,5),(174,(0,0))),((3,4),(175,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_52_checked : successorFastRowCheck layer8 row7_52 row7_52choice = true := by decide
def row7_53 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3)]
def row7_53choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(846,(1,0))),((-1,1),(1512,(1,0))),((-1,2),(2100,(1,0))),((-1,3),(2494,(1,0))),((0,-1),(78,(0,1))),((0,4),(72,(0,0))),((1,0),(111,(0,0))),((1,1),(136,(0,0))),((1,2),(153,(0,0))),((1,4),(171,(0,0))),((2,1),(176,(0,0))),((2,4),(177,(0,0))),((3,2),(178,(0,0))),((3,3),(179,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_53_checked : successorFastRowCheck layer8 row7_53 row7_53choice = true := by decide
def row7_54 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4)]
def row7_54choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(847,(1,0))),((-1,1),(1513,(1,0))),((-1,2),(2101,(1,0))),((-1,3),(2495,(1,0))),((0,-1),(79,(0,1))),((0,4),(73,(0,0))),((1,0),(112,(0,0))),((1,1),(137,(0,0))),((1,2),(155,(0,0))),((1,4),(172,(0,0))),((2,2),(177,(0,0))),((2,5),(180,(0,0))),((3,3),(181,(0,0))),((3,4),(182,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_54_checked : successorFastRowCheck layer8 row7_54 row7_54choice = true := by decide
def row7_55 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3)]
def row7_55choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(848,(1,0))),((-1,1),(1514,(1,0))),((-1,2),(2102,(1,0))),((-1,3),(2496,(1,0))),((0,-1),(80,(0,1))),((0,4),(74,(0,0))),((1,0),(113,(0,0))),((1,1),(138,(0,0))),((1,2),(156,(0,0))),((1,4),(173,(0,0))),((2,2),(179,(0,0))),((2,4),(181,(0,0))),((3,2),(183,(0,0))),((3,4),(184,(0,0))),((4,3),(185,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_55_checked : successorFastRowCheck layer8 row7_55 row7_55choice = true := by decide
def Closure7C006rows : List (List GridPoint) := [row7_48,row7_49,row7_50,row7_51,row7_52,row7_53,row7_54,row7_55]
theorem Closure7C006_closed : ∀ row ∈ Closure7C006rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C006rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_48choice,row7_48_checked⟩
  · subst row
    exact ⟨row7_49choice,row7_49_checked⟩
  · subst row
    exact ⟨row7_50choice,row7_50_checked⟩
  · subst row
    exact ⟨row7_51choice,row7_51_checked⟩
  · subst row
    exact ⟨row7_52choice,row7_52_checked⟩
  · subst row
    exact ⟨row7_53choice,row7_53_checked⟩
  · subst row
    exact ⟨row7_54choice,row7_54_checked⟩
  · subst row
    exact ⟨row7_55choice,row7_55_checked⟩
end Polyomino57
