import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_336 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)]
def row7_336choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1129,(1,0))),((0,-1),(667,(0,1))),((0,1),(506,(0,0))),((1,-1),(1645,(0,1))),((1,1),(937,(0,0))),((2,-1),(1792,(0,1))),((2,2),(1062,(0,0))),((3,0),(1076,(0,0))),((3,2),(1089,(0,0))),((4,-1),(1846,(0,1))),((4,2),(1094,(0,0))),((5,0),(1095,(0,0))),((5,1),(1096,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_336_checked : successorFastRowCheck layer8 row7_336 row7_336choice = true := by decide
def row7_337 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)]
def row7_337choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1130,(1,0))),((0,-1),(668,(0,1))),((0,1),(507,(0,0))),((1,-1),(1646,(0,1))),((1,1),(938,(0,0))),((2,-1),(1793,(0,1))),((2,2),(1063,(0,0))),((3,0),(1078,(0,0))),((3,2),(1090,(0,0))),((4,0),(1094,(0,0))),((4,3),(1097,(0,0))),((5,1),(1098,(0,0))),((5,2),(1099,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_337_checked : successorFastRowCheck layer8 row7_337 row7_337choice = true := by decide
def row7_338 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)]
def row7_338choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1131,(1,0))),((0,-1),(669,(0,1))),((0,1),(508,(0,0))),((1,-1),(1647,(0,1))),((1,1),(939,(0,0))),((2,-1),(1794,(0,1))),((2,2),(1064,(0,0))),((3,0),(1079,(0,0))),((3,2),(1091,(0,0))),((4,0),(1096,(0,0))),((4,2),(1098,(0,0))),((5,0),(1100,(0,0))),((5,2),(1101,(0,0))),((6,1),(1102,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_338_checked : successorFastRowCheck layer8 row7_338 row7_338choice = true := by decide
def row7_339 : List GridPoint := [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)]
def row7_339choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1132,(1,0))),((0,-1),(670,(0,1))),((0,1),(509,(0,0))),((1,-1),(1648,(0,1))),((1,1),(940,(0,0))),((1,2),(1026,(0,0))),((2,-1),(1795,(0,1))),((2,1),(1051,(0,0))),((2,3),(1103,(0,0))),((3,-1),(1847,(0,1))),((3,3),(1104,(0,0))),((4,0),(1105,(0,0))),((4,1),(1106,(0,0))),((4,2),(1107,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_339_checked : successorFastRowCheck layer8 row7_339 row7_339choice = true := by decide
def row7_340 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)]
def row7_340choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1133,(1,0))),((0,-1),(679,(0,1))),((0,1),(510,(0,0))),((1,-1),(1657,(0,1))),((1,1),(941,(0,0))),((2,-1),(1809,(0,1))),((2,1),(1072,(0,0))),((2,2),(1104,(0,0))),((2,3),(1108,(0,0))),((3,-1),(1848,(0,1))),((3,4),(1109,(0,0))),((4,0),(1110,(0,0))),((4,1),(1111,(0,0))),((4,2),(1112,(0,0))),((4,3),(1113,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_340_checked : successorFastRowCheck layer8 row7_340 row7_340choice = true := by decide
def row7_341 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)]
def row7_341choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1134,(1,0))),((0,-1),(680,(0,1))),((0,1),(511,(0,0))),((1,-1),(1658,(0,1))),((1,1),(942,(0,0))),((2,-1),(1810,(0,1))),((2,1),(1073,(0,0))),((2,2),(1105,(0,0))),((3,-1),(1850,(0,1))),((3,3),(1110,(0,0))),((4,-1),(1871,(0,1))),((4,1),(1114,(0,0))),((4,2),(1115,(0,0))),((5,0),(1116,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_341_checked : successorFastRowCheck layer8 row7_341 row7_341choice = true := by decide
def row7_342 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)]
def row7_342choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1135,(1,0))),((0,-1),(681,(0,1))),((0,1),(512,(0,0))),((1,-1),(1659,(0,1))),((1,1),(943,(0,0))),((2,-1),(1811,(0,1))),((2,1),(1074,(0,0))),((2,2),(1106,(0,0))),((3,-1),(1851,(0,1))),((3,3),(1111,(0,0))),((4,0),(1114,(0,0))),((4,2),(1117,(0,0))),((5,1),(1118,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_342_checked : successorFastRowCheck layer8 row7_342 row7_342choice = true := by decide
def row7_343 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)]
def row7_343choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1136,(1,0))),((0,-1),(682,(0,1))),((0,1),(513,(0,0))),((1,-1),(1660,(0,1))),((1,1),(944,(0,0))),((2,-1),(1812,(0,1))),((2,1),(1075,(0,0))),((2,2),(1107,(0,0))),((3,-1),(1852,(0,1))),((3,3),(1112,(0,0))),((4,0),(1115,(0,0))),((4,1),(1117,(0,0))),((4,3),(1119,(0,0))),((5,2),(1120,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_343_checked : successorFastRowCheck layer8 row7_343 row7_343choice = true := by decide
def Closure7C042rows : List (List GridPoint) := [row7_336,row7_337,row7_338,row7_339,row7_340,row7_341,row7_342,row7_343]
theorem Closure7C042_closed : ∀ row ∈ Closure7C042rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C042rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_336choice,row7_336_checked⟩
  · subst row
    exact ⟨row7_337choice,row7_337_checked⟩
  · subst row
    exact ⟨row7_338choice,row7_338_checked⟩
  · subst row
    exact ⟨row7_339choice,row7_339_checked⟩
  · subst row
    exact ⟨row7_340choice,row7_340_checked⟩
  · subst row
    exact ⟨row7_341choice,row7_341_checked⟩
  · subst row
    exact ⟨row7_342choice,row7_342_checked⟩
  · subst row
    exact ⟨row7_343choice,row7_343_checked⟩
end Polyomino57
