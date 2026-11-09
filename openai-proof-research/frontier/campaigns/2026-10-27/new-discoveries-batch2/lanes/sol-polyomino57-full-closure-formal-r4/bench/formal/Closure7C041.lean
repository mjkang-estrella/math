import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_328 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)]
def row7_328choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1121,(1,0))),((0,-1),(658,(0,1))),((0,1),(498,(0,0))),((1,-1),(1636,(0,1))),((1,1),(929,(0,0))),((2,-1),(1783,(0,1))),((2,2),(1051,(0,0))),((3,-1),(1833,(0,1))),((3,3),(1072,(0,0))),((4,0),(1073,(0,0))),((4,1),(1074,(0,0))),((4,2),(1075,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_328_checked : successorFastRowCheck layer8 row7_328 row7_328choice = true := by decide
def row7_329 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)]
def row7_329choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1122,(1,0))),((0,-1),(659,(0,1))),((0,1),(499,(0,0))),((1,-1),(1637,(0,1))),((1,1),(930,(0,0))),((2,-1),(1784,(0,1))),((2,2),(1052,(0,0))),((3,-1),(1835,(0,1))),((3,2),(1073,(0,0))),((4,-1),(1841,(0,1))),((4,1),(1076,(0,0))),((5,0),(1077,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_329_checked : successorFastRowCheck layer8 row7_329 row7_329choice = true := by decide
def row7_330 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)]
def row7_330choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1123,(1,0))),((0,-1),(660,(0,1))),((0,1),(500,(0,0))),((1,-1),(1638,(0,1))),((1,1),(931,(0,0))),((2,-1),(1785,(0,1))),((2,2),(1053,(0,0))),((3,-1),(1836,(0,1))),((3,2),(1074,(0,0))),((4,0),(1076,(0,0))),((4,2),(1078,(0,0))),((5,1),(1079,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_330_checked : successorFastRowCheck layer8 row7_330 row7_330choice = true := by decide
def row7_331 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)]
def row7_331choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1124,(1,0))),((0,-1),(662,(0,1))),((0,1),(501,(0,0))),((1,-1),(1640,(0,1))),((1,1),(932,(0,0))),((2,-1),(1787,(0,1))),((2,2),(1057,(0,0))),((3,-1),(1839,(0,1))),((3,1),(1076,(0,0))),((4,-1),(1842,(0,1))),((4,2),(1080,(0,0))),((5,0),(1081,(0,0))),((5,1),(1082,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_331_checked : successorFastRowCheck layer8 row7_331 row7_331choice = true := by decide
def row7_332 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)]
def row7_332choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1125,(1,0))),((0,-1),(663,(0,1))),((0,1),(502,(0,0))),((1,-1),(1641,(0,1))),((1,1),(933,(0,0))),((2,-1),(1788,(0,1))),((2,2),(1058,(0,0))),((3,-1),(1840,(0,1))),((3,1),(1077,(0,0))),((4,-1),(1844,(0,1))),((4,1),(1081,(0,0))),((5,-1),(1845,(0,1))),((5,1),(1083,(0,0))),((6,0),(1084,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_332_checked : successorFastRowCheck layer8 row7_332 row7_332choice = true := by decide
def row7_333 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)]
def row7_333choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1126,(1,0))),((0,-1),(664,(0,1))),((0,1),(503,(0,0))),((1,-1),(1642,(0,1))),((1,1),(934,(0,0))),((2,-1),(1789,(0,1))),((2,2),(1059,(0,0))),((2,3),(1071,(0,0))),((3,0),(1072,(0,0))),((3,4),(1085,(0,0))),((4,1),(1086,(0,0))),((4,2),(1087,(0,0))),((4,3),(1088,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_333_checked : successorFastRowCheck layer8 row7_333 row7_333choice = true := by decide
def row7_334 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)]
def row7_334choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1127,(1,0))),((0,-1),(665,(0,1))),((0,1),(504,(0,0))),((1,-1),(1643,(0,1))),((1,1),(935,(0,0))),((2,-1),(1790,(0,1))),((2,2),(1060,(0,0))),((3,0),(1074,(0,0))),((3,3),(1086,(0,0))),((4,0),(1089,(0,0))),((4,2),(1090,(0,0))),((5,1),(1091,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_334_checked : successorFastRowCheck layer8 row7_334 row7_334choice = true := by decide
def row7_335 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)]
def row7_335choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1128,(1,0))),((0,-1),(666,(0,1))),((0,1),(505,(0,0))),((1,-1),(1644,(0,1))),((1,1),(936,(0,0))),((2,-1),(1791,(0,1))),((2,2),(1061,(0,0))),((3,0),(1075,(0,0))),((3,3),(1087,(0,0))),((4,1),(1090,(0,0))),((4,3),(1092,(0,0))),((5,2),(1093,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_335_checked : successorFastRowCheck layer8 row7_335 row7_335choice = true := by decide
def Closure7C041rows : List (List GridPoint) := [row7_328,row7_329,row7_330,row7_331,row7_332,row7_333,row7_334,row7_335]
theorem Closure7C041_closed : ∀ row ∈ Closure7C041rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C041rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_328choice,row7_328_checked⟩
  · subst row
    exact ⟨row7_329choice,row7_329_checked⟩
  · subst row
    exact ⟨row7_330choice,row7_330_checked⟩
  · subst row
    exact ⟨row7_331choice,row7_331_checked⟩
  · subst row
    exact ⟨row7_332choice,row7_332_checked⟩
  · subst row
    exact ⟨row7_333choice,row7_333_checked⟩
  · subst row
    exact ⟨row7_334choice,row7_334_checked⟩
  · subst row
    exact ⟨row7_335choice,row7_335_checked⟩
end Polyomino57
