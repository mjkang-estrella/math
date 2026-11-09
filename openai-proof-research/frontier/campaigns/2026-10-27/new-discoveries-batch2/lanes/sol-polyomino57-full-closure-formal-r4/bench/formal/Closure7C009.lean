import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_72 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2)]
def row7_72choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(865,(1,0))),((-1,1),(1531,(1,0))),((-1,2),(2119,(1,0))),((0,-1),(136,(0,1))),((0,3),(101,(0,0))),((1,-1),(1202,(0,1))),((1,1),(202,(0,0))),((1,3),(226,(0,0))),((2,0),(231,(0,0))),((2,3),(239,(0,0))),((3,1),(240,(0,0))),((3,2),(241,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_72_checked : successorFastRowCheck layer8 row7_72 row7_72choice = true := by decide
def row7_73 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3)]
def row7_73choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(866,(1,0))),((-1,1),(1532,(1,0))),((-1,2),(2120,(1,0))),((0,-1),(137,(0,1))),((0,3),(102,(0,0))),((1,-1),(1203,(0,1))),((1,1),(204,(0,0))),((1,3),(227,(0,0))),((2,0),(234,(0,0))),((2,1),(239,(0,0))),((2,4),(242,(0,0))),((3,2),(243,(0,0))),((3,3),(244,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_73_checked : successorFastRowCheck layer8 row7_73 row7_73choice = true := by decide
def row7_74 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2)]
def row7_74choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(867,(1,0))),((-1,1),(1533,(1,0))),((-1,2),(2121,(1,0))),((0,-1),(138,(0,1))),((0,3),(103,(0,0))),((1,-1),(1204,(0,1))),((1,1),(205,(0,0))),((1,3),(228,(0,0))),((2,0),(236,(0,0))),((2,1),(241,(0,0))),((2,3),(243,(0,0))),((3,1),(245,(0,0))),((3,3),(246,(0,0))),((4,2),(247,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_74_checked : successorFastRowCheck layer8 row7_74 row7_74choice = true := by decide
def row7_75 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2)]
def row7_75choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(868,(1,0))),((-1,1),(1534,(1,0))),((-1,2),(2122,(1,0))),((0,-1),(142,(0,1))),((0,3),(114,(0,0))),((1,-1),(1210,(0,1))),((1,1),(206,(0,0))),((1,2),(231,(0,0))),((2,-1),(1228,(0,1))),((2,3),(248,(0,0))),((3,0),(249,(0,0))),((3,1),(250,(0,0))),((3,2),(251,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_75_checked : successorFastRowCheck layer8 row7_75 row7_75choice = true := by decide
def row7_76 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0)]
def row7_76choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(869,(1,0))),((-1,1),(1535,(1,0))),((-1,2),(2123,(1,0))),((0,-1),(143,(0,1))),((0,3),(115,(0,0))),((1,-1),(1211,(0,1))),((1,1),(207,(0,0))),((1,2),(232,(0,0))),((2,-1),(1230,(0,1))),((2,2),(249,(0,0))),((3,-1),(1236,(0,1))),((3,1),(252,(0,0))),((4,0),(253,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_76_checked : successorFastRowCheck layer8 row7_76 row7_76choice = true := by decide
def row7_77 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1)]
def row7_77choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(870,(1,0))),((-1,1),(1536,(1,0))),((-1,2),(2124,(1,0))),((0,-1),(144,(0,1))),((0,3),(116,(0,0))),((1,-1),(1212,(0,1))),((1,1),(208,(0,0))),((1,2),(233,(0,0))),((2,-1),(1231,(0,1))),((2,2),(250,(0,0))),((3,0),(252,(0,0))),((3,2),(254,(0,0))),((4,1),(255,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_77_checked : successorFastRowCheck layer8 row7_77 row7_77choice = true := by decide
def row7_78 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1)]
def row7_78choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(871,(1,0))),((-1,1),(1537,(1,0))),((-1,2),(2125,(1,0))),((0,-1),(146,(0,1))),((0,3),(117,(0,0))),((1,-1),(1214,(0,1))),((1,1),(209,(0,0))),((1,2),(237,(0,0))),((2,-1),(1234,(0,1))),((2,1),(252,(0,0))),((3,-1),(1237,(0,1))),((3,2),(256,(0,0))),((4,0),(257,(0,0))),((4,1),(258,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_78_checked : successorFastRowCheck layer8 row7_78 row7_78choice = true := by decide
def row7_79 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0)]
def row7_79choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(872,(1,0))),((-1,1),(1538,(1,0))),((-1,2),(2126,(1,0))),((0,-1),(147,(0,1))),((0,3),(118,(0,0))),((1,-1),(1215,(0,1))),((1,1),(210,(0,0))),((1,2),(238,(0,0))),((2,-1),(1235,(0,1))),((2,1),(253,(0,0))),((3,-1),(1239,(0,1))),((3,1),(257,(0,0))),((4,-1),(1240,(0,1))),((4,1),(259,(0,0))),((5,0),(260,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_79_checked : successorFastRowCheck layer8 row7_79 row7_79choice = true := by decide
def Closure7C009rows : List (List GridPoint) := [row7_72,row7_73,row7_74,row7_75,row7_76,row7_77,row7_78,row7_79]
theorem Closure7C009_closed : ∀ row ∈ Closure7C009rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C009rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_72choice,row7_72_checked⟩
  · subst row
    exact ⟨row7_73choice,row7_73_checked⟩
  · subst row
    exact ⟨row7_74choice,row7_74_checked⟩
  · subst row
    exact ⟨row7_75choice,row7_75_checked⟩
  · subst row
    exact ⟨row7_76choice,row7_76_checked⟩
  · subst row
    exact ⟨row7_77choice,row7_77_checked⟩
  · subst row
    exact ⟨row7_78choice,row7_78_checked⟩
  · subst row
    exact ⟨row7_79choice,row7_79_checked⟩
end Polyomino57
