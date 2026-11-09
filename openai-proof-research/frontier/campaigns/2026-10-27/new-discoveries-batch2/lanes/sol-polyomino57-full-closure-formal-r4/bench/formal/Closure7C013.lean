import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_104 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2)]
def row7_104choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(897,(1,0))),((-1,1),(1563,(1,0))),((-1,2),(2151,(1,0))),((0,-1),(173,(0,1))),((0,3),(154,(0,0))),((1,0),(228,(0,0))),((1,1),(271,(0,0))),((1,4),(324,(0,0))),((2,1),(332,(0,0))),((2,3),(334,(0,0))),((3,1),(336,(0,0))),((3,3),(337,(0,0))),((4,2),(338,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_104_checked : successorFastRowCheck layer8 row7_104 row7_104choice = true := by decide
def row7_105 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4)]
def row7_105choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(898,(1,0))),((-1,1),(1564,(1,0))),((-1,2),(2152,(1,0))),((0,-1),(174,(0,1))),((0,3),(155,(0,0))),((1,0),(229,(0,0))),((1,1),(272,(0,0))),((1,4),(325,(0,0))),((2,2),(333,(0,0))),((2,5),(339,(0,0))),((3,3),(340,(0,0))),((3,4),(341,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_105_checked : successorFastRowCheck layer8 row7_105 row7_105choice = true := by decide
def row7_106 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3)]
def row7_106choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(899,(1,0))),((-1,1),(1565,(1,0))),((-1,2),(2153,(1,0))),((0,-1),(175,(0,1))),((0,3),(156,(0,0))),((1,0),(230,(0,0))),((1,1),(273,(0,0))),((1,4),(326,(0,0))),((2,2),(335,(0,0))),((2,4),(340,(0,0))),((3,2),(342,(0,0))),((3,4),(343,(0,0))),((4,3),(344,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_106_checked : successorFastRowCheck layer8 row7_106 row7_106choice = true := by decide
def row7_107 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2)]
def row7_107choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(900,(1,0))),((-1,1),(1566,(1,0))),((-1,2),(2154,(1,0))),((0,-1),(176,(0,1))),((0,3),(157,(0,0))),((1,0),(231,(0,0))),((1,1),(274,(0,0))),((1,3),(329,(0,0))),((2,-1),(1248,(0,1))),((2,3),(346,(0,0))),((3,0),(347,(0,0))),((3,1),(348,(0,0))),((3,2),(349,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_107_checked : successorFastRowCheck layer8 row7_107 row7_107choice = true := by decide
def row7_108 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3)]
def row7_108choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(901,(1,0))),((-1,1),(1567,(1,0))),((-1,2),(2155,(1,0))),((0,-1),(177,(0,1))),((0,3),(158,(0,0))),((1,0),(239,(0,0))),((1,1),(277,(0,0))),((1,3),(330,(0,0))),((2,0),(346,(0,0))),((2,4),(350,(0,0))),((3,1),(351,(0,0))),((3,2),(352,(0,0))),((3,3),(353,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_108_checked : successorFastRowCheck layer8 row7_108 row7_108choice = true := by decide
def row7_109 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1)]
def row7_109choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(902,(1,0))),((-1,1),(1568,(1,0))),((-1,2),(2156,(1,0))),((0,-1),(178,(0,1))),((0,3),(159,(0,0))),((1,0),(240,(0,0))),((1,1),(278,(0,0))),((1,3),(331,(0,0))),((2,0),(348,(0,0))),((2,3),(351,(0,0))),((3,0),(354,(0,0))),((3,2),(355,(0,0))),((4,1),(356,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_109_checked : successorFastRowCheck layer8 row7_109 row7_109choice = true := by decide
def row7_110 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2)]
def row7_110choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(903,(1,0))),((-1,1),(1569,(1,0))),((-1,2),(2157,(1,0))),((0,-1),(179,(0,1))),((0,3),(160,(0,0))),((1,0),(241,(0,0))),((1,1),(279,(0,0))),((1,3),(332,(0,0))),((2,0),(349,(0,0))),((2,3),(352,(0,0))),((3,1),(355,(0,0))),((3,3),(357,(0,0))),((4,2),(358,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_110_checked : successorFastRowCheck layer8 row7_110 row7_110choice = true := by decide
def row7_111 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4)]
def row7_111choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(904,(1,0))),((-1,1),(1570,(1,0))),((-1,2),(2158,(1,0))),((0,-1),(180,(0,1))),((0,3),(161,(0,0))),((1,0),(242,(0,0))),((1,1),(283,(0,0))),((1,3),(333,(0,0))),((1,4),(345,(0,0))),((2,1),(350,(0,0))),((2,5),(359,(0,0))),((3,2),(360,(0,0))),((3,3),(361,(0,0))),((3,4),(362,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_111_checked : successorFastRowCheck layer8 row7_111 row7_111choice = true := by decide
def Closure7C013rows : List (List GridPoint) := [row7_104,row7_105,row7_106,row7_107,row7_108,row7_109,row7_110,row7_111]
theorem Closure7C013_closed : ∀ row ∈ Closure7C013rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C013rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_104choice,row7_104_checked⟩
  · subst row
    exact ⟨row7_105choice,row7_105_checked⟩
  · subst row
    exact ⟨row7_106choice,row7_106_checked⟩
  · subst row
    exact ⟨row7_107choice,row7_107_checked⟩
  · subst row
    exact ⟨row7_108choice,row7_108_checked⟩
  · subst row
    exact ⟨row7_109choice,row7_109_checked⟩
  · subst row
    exact ⟨row7_110choice,row7_110_checked⟩
  · subst row
    exact ⟨row7_111choice,row7_111_checked⟩
end Polyomino57
