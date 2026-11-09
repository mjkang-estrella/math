import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_32 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3)]
def row7_32choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(825,(1,0))),((-1,1),(1491,(1,0))),((-1,2),(2079,(1,0))),((-1,3),(2473,(1,0))),((0,-1),(56,(0,1))),((0,4),(41,(0,0))),((1,-1),(1166,(0,1))),((1,1),(89,(0,0))),((1,2),(97,(0,0))),((1,4),(106,(0,0))),((2,0),(109,(0,0))),((2,2),(111,(0,0))),((2,4),(112,(0,0))),((3,3),(113,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_32_checked : successorFastRowCheck layer8 row7_32 row7_32choice = true := by decide
def row7_33 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1)]
def row7_33choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(826,(1,0))),((-1,1),(1492,(1,0))),((-1,2),(2080,(1,0))),((-1,3),(2474,(1,0))),((0,-1),(58,(0,1))),((0,4),(45,(0,0))),((1,-1),(1169,(0,1))),((1,1),(90,(0,0))),((1,2),(98,(0,0))),((1,3),(108,(0,0))),((2,-1),(1174,(0,1))),((2,2),(114,(0,0))),((3,0),(115,(0,0))),((3,1),(116,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_33_checked : successorFastRowCheck layer8 row7_33 row7_33choice = true := by decide
def row7_34 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0)]
def row7_34choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(827,(1,0))),((-1,1),(1493,(1,0))),((-1,2),(2081,(1,0))),((-1,3),(2475,(1,0))),((0,-1),(59,(0,1))),((0,4),(46,(0,0))),((1,-1),(1170,(0,1))),((1,1),(91,(0,0))),((1,2),(100,(0,0))),((1,3),(110,(0,0))),((2,-1),(1176,(0,1))),((2,1),(115,(0,0))),((3,-1),(1177,(0,1))),((3,1),(117,(0,0))),((4,0),(118,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_34_checked : successorFastRowCheck layer8 row7_34 row7_34choice = true := by decide
def row7_35 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3)]
def row7_35choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(828,(1,0))),((-1,1),(1494,(1,0))),((-1,2),(2082,(1,0))),((-1,3),(2476,(1,0))),((0,-1),(60,(0,1))),((0,4),(47,(0,0))),((1,0),(82,(0,0))),((1,4),(119,(0,0))),((2,1),(120,(0,0))),((2,2),(121,(0,0))),((2,3),(122,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_35_checked : successorFastRowCheck layer8 row7_35 row7_35choice = true := by decide
def row7_36 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1)]
def row7_36choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(829,(1,0))),((-1,1),(1495,(1,0))),((-1,2),(2083,(1,0))),((-1,3),(2477,(1,0))),((0,-1),(61,(0,1))),((0,4),(49,(0,0))),((1,0),(84,(0,0))),((1,3),(120,(0,0))),((2,0),(123,(0,0))),((2,2),(124,(0,0))),((3,1),(125,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_36_checked : successorFastRowCheck layer8 row7_36 row7_36choice = true := by decide
def row7_37 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2)]
def row7_37choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(830,(1,0))),((-1,1),(1496,(1,0))),((-1,2),(2084,(1,0))),((-1,3),(2478,(1,0))),((0,-1),(62,(0,1))),((0,4),(50,(0,0))),((1,0),(85,(0,0))),((1,3),(121,(0,0))),((2,1),(124,(0,0))),((2,3),(126,(0,0))),((3,2),(127,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_37_checked : successorFastRowCheck layer8 row7_37 row7_37choice = true := by decide
def row7_38 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4)]
def row7_38choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(831,(1,0))),((-1,1),(1497,(1,0))),((-1,2),(2085,(1,0))),((-1,3),(2479,(1,0))),((0,-1),(63,(0,1))),((0,4),(51,(0,0))),((1,0),(86,(0,0))),((1,2),(119,(0,0))),((1,5),(128,(0,0))),((2,1),(129,(0,0))),((2,3),(130,(0,0))),((2,4),(131,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_38_checked : successorFastRowCheck layer8 row7_38 row7_38choice = true := by decide
def row7_39 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1)]
def row7_39choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(832,(1,0))),((-1,1),(1498,(1,0))),((-1,2),(2086,(1,0))),((-1,3),(2480,(1,0))),((0,-1),(64,(0,1))),((0,4),(52,(0,0))),((1,0),(88,(0,0))),((1,2),(120,(0,0))),((1,4),(129,(0,0))),((2,0),(132,(0,0))),((2,2),(133,(0,0))),((2,3),(134,(0,0))),((3,1),(135,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_39_checked : successorFastRowCheck layer8 row7_39 row7_39choice = true := by decide
def Closure7C004rows : List (List GridPoint) := [row7_32,row7_33,row7_34,row7_35,row7_36,row7_37,row7_38,row7_39]
theorem Closure7C004_closed : ∀ row ∈ Closure7C004rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C004rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_32choice,row7_32_checked⟩
  · subst row
    exact ⟨row7_33choice,row7_33_checked⟩
  · subst row
    exact ⟨row7_34choice,row7_34_checked⟩
  · subst row
    exact ⟨row7_35choice,row7_35_checked⟩
  · subst row
    exact ⟨row7_36choice,row7_36_checked⟩
  · subst row
    exact ⟨row7_37choice,row7_37_checked⟩
  · subst row
    exact ⟨row7_38choice,row7_38_checked⟩
  · subst row
    exact ⟨row7_39choice,row7_39_checked⟩
end Polyomino57
