import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_56 : List GridPoint := [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4)]
def row7_56choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(849,(1,0))),((-1,1),(1515,(1,0))),((-1,2),(2103,(1,0))),((-1,4),(2667,(1,0))),((0,-1),(81,(0,1))),((0,3),(60,(0,0))),((0,5),(186,(0,0))),((1,0),(187,(0,0))),((1,1),(188,(0,0))),((1,5),(189,(0,0))),((2,2),(190,(0,0))),((2,3),(191,(0,0))),((2,4),(192,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_56_checked : successorFastRowCheck layer8 row7_56 row7_56choice = true := by decide
def row7_57 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3)]
def row7_57choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(850,(1,0))),((-1,1),(1516,(1,0))),((-1,2),(2104,(1,0))),((0,-1),(119,(0,1))),((0,3),(82,(0,0))),((1,-1),(1179,(0,1))),((1,4),(194,(0,0))),((2,0),(195,(0,0))),((2,1),(196,(0,0))),((2,2),(197,(0,0))),((2,3),(198,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_57_checked : successorFastRowCheck layer8 row7_57 row7_57choice = true := by decide
def row7_58 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0)]
def row7_58choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(851,(1,0))),((-1,1),(1517,(1,0))),((-1,2),(2105,(1,0))),((0,-1),(120,(0,1))),((0,3),(83,(0,0))),((1,-1),(1181,(0,1))),((1,3),(195,(0,0))),((2,-1),(1217,(0,1))),((2,1),(199,(0,0))),((2,2),(200,(0,0))),((3,0),(201,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_58_checked : successorFastRowCheck layer8 row7_58 row7_58choice = true := by decide
def row7_59 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1)]
def row7_59choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(852,(1,0))),((-1,1),(1518,(1,0))),((-1,2),(2106,(1,0))),((0,-1),(121,(0,1))),((0,3),(84,(0,0))),((1,-1),(1182,(0,1))),((1,3),(196,(0,0))),((2,0),(199,(0,0))),((2,2),(202,(0,0))),((3,1),(203,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_59_checked : successorFastRowCheck layer8 row7_59 row7_59choice = true := by decide
def row7_60 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2)]
def row7_60choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(853,(1,0))),((-1,1),(1519,(1,0))),((-1,2),(2107,(1,0))),((0,-1),(122,(0,1))),((0,3),(85,(0,0))),((1,-1),(1183,(0,1))),((1,3),(197,(0,0))),((2,0),(200,(0,0))),((2,1),(202,(0,0))),((2,3),(204,(0,0))),((3,2),(205,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_60_checked : successorFastRowCheck layer8 row7_60 row7_60choice = true := by decide
def row7_61 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1)]
def row7_61choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(854,(1,0))),((-1,1),(1520,(1,0))),((-1,2),(2108,(1,0))),((0,-1),(124,(0,1))),((0,3),(90,(0,0))),((1,-1),(1187,(0,1))),((1,2),(199,(0,0))),((2,-1),(1218,(0,1))),((2,2),(206,(0,0))),((3,0),(207,(0,0))),((3,1),(208,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_61_checked : successorFastRowCheck layer8 row7_61 row7_61choice = true := by decide
def row7_62 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0)]
def row7_62choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(855,(1,0))),((-1,1),(1521,(1,0))),((-1,2),(2109,(1,0))),((0,-1),(125,(0,1))),((0,3),(91,(0,0))),((1,-1),(1188,(0,1))),((1,2),(201,(0,0))),((2,-1),(1220,(0,1))),((2,1),(207,(0,0))),((3,-1),(1221,(0,1))),((3,1),(209,(0,0))),((4,0),(210,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_62_checked : successorFastRowCheck layer8 row7_62 row7_62choice = true := by decide
def row7_63 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2)]
def row7_63choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(856,(1,0))),((-1,1),(1522,(1,0))),((-1,2),(2110,(1,0))),((0,-1),(126,(0,1))),((0,3),(92,(0,0))),((1,-1),(1189,(0,1))),((1,2),(202,(0,0))),((2,0),(206,(0,0))),((2,3),(211,(0,0))),((3,1),(212,(0,0))),((3,2),(213,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_63_checked : successorFastRowCheck layer8 row7_63 row7_63choice = true := by decide
def Closure7C007rows : List (List GridPoint) := [row7_56,row7_57,row7_58,row7_59,row7_60,row7_61,row7_62,row7_63]
theorem Closure7C007_closed : ∀ row ∈ Closure7C007rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C007rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_56choice,row7_56_checked⟩
  · subst row
    exact ⟨row7_57choice,row7_57_checked⟩
  · subst row
    exact ⟨row7_58choice,row7_58_checked⟩
  · subst row
    exact ⟨row7_59choice,row7_59_checked⟩
  · subst row
    exact ⟨row7_60choice,row7_60_checked⟩
  · subst row
    exact ⟨row7_61choice,row7_61_checked⟩
  · subst row
    exact ⟨row7_62choice,row7_62_checked⟩
  · subst row
    exact ⟨row7_63choice,row7_63_checked⟩
end Polyomino57
