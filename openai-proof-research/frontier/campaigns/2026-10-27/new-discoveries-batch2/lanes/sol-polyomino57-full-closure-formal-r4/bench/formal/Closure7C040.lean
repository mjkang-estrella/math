import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_320 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)]
def row7_320choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1113,(1,0))),((0,-1),(646,(0,1))),((0,1),(490,(0,0))),((1,-1),(1624,(0,1))),((1,1),(921,(0,0))),((1,2),(1018,(0,0))),((1,3),(1032,(0,0))),((2,-1),(1763,(0,1))),((2,4),(1038,(0,0))),((3,0),(1042,(0,0))),((3,1),(1045,(0,0))),((3,2),(1047,(0,0))),((3,4),(1049,(0,0))),((4,3),(1050,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_320_checked : successorFastRowCheck layer8 row7_320 row7_320choice = true := by decide
def row7_321 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)]
def row7_321choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1114,(1,0))),((0,-1),(648,(0,1))),((0,1),(491,(0,0))),((1,-1),(1626,(0,1))),((1,1),(922,(0,0))),((1,2),(1019,(0,0))),((2,-1),(1768,(0,1))),((2,3),(1040,(0,0))),((3,-1),(1828,(0,1))),((3,2),(1051,(0,0))),((4,0),(1052,(0,0))),((4,1),(1053,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_321_checked : successorFastRowCheck layer8 row7_321 row7_321choice = true := by decide
def row7_322 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)]
def row7_322choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1115,(1,0))),((0,-1),(649,(0,1))),((0,1),(492,(0,0))),((1,-1),(1627,(0,1))),((1,1),(923,(0,0))),((1,2),(1020,(0,0))),((2,-1),(1769,(0,1))),((2,3),(1041,(0,0))),((3,-1),(1829,(0,1))),((3,1),(1051,(0,0))),((3,3),(1054,(0,0))),((4,0),(1055,(0,0))),((4,2),(1056,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_322_checked : successorFastRowCheck layer8 row7_322 row7_322choice = true := by decide
def row7_323 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)]
def row7_323choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1116,(1,0))),((0,-1),(650,(0,1))),((0,1),(493,(0,0))),((1,-1),(1628,(0,1))),((1,1),(924,(0,0))),((1,2),(1021,(0,0))),((2,-1),(1770,(0,1))),((2,3),(1043,(0,0))),((3,-1),(1831,(0,1))),((3,1),(1052,(0,0))),((3,2),(1055,(0,0))),((4,-1),(1832,(0,1))),((4,1),(1057,(0,0))),((5,0),(1058,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_323_checked : successorFastRowCheck layer8 row7_323 row7_323choice = true := by decide
def row7_324 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)]
def row7_324choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1117,(1,0))),((0,-1),(651,(0,1))),((0,1),(494,(0,0))),((1,-1),(1629,(0,1))),((1,1),(925,(0,0))),((1,2),(1022,(0,0))),((2,-1),(1771,(0,1))),((2,3),(1044,(0,0))),((3,0),(1051,(0,0))),((3,3),(1059,(0,0))),((4,1),(1060,(0,0))),((4,2),(1061,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_324_checked : successorFastRowCheck layer8 row7_324 row7_324choice = true := by decide
def row7_325 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)]
def row7_325choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1118,(1,0))),((0,-1),(652,(0,1))),((0,1),(495,(0,0))),((1,-1),(1630,(0,1))),((1,1),(926,(0,0))),((1,2),(1023,(0,0))),((2,-1),(1772,(0,1))),((2,3),(1046,(0,0))),((3,0),(1053,(0,0))),((3,2),(1060,(0,0))),((4,0),(1062,(0,0))),((4,2),(1063,(0,0))),((5,1),(1064,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_325_checked : successorFastRowCheck layer8 row7_325 row7_325choice = true := by decide
def row7_326 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)]
def row7_326choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1119,(1,0))),((0,-1),(653,(0,1))),((0,1),(496,(0,0))),((1,-1),(1631,(0,1))),((1,1),(927,(0,0))),((1,2),(1024,(0,0))),((2,-1),(1773,(0,1))),((2,3),(1047,(0,0))),((3,0),(1054,(0,0))),((3,1),(1059,(0,0))),((3,4),(1065,(0,0))),((4,2),(1066,(0,0))),((4,3),(1067,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_326_checked : successorFastRowCheck layer8 row7_326 row7_326choice = true := by decide
def row7_327 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)]
def row7_327choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1120,(1,0))),((0,-1),(654,(0,1))),((0,1),(497,(0,0))),((1,-1),(1632,(0,1))),((1,1),(928,(0,0))),((1,2),(1025,(0,0))),((2,-1),(1774,(0,1))),((2,3),(1048,(0,0))),((3,0),(1056,(0,0))),((3,1),(1061,(0,0))),((3,3),(1066,(0,0))),((4,1),(1068,(0,0))),((4,3),(1069,(0,0))),((5,2),(1070,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_327_checked : successorFastRowCheck layer8 row7_327 row7_327choice = true := by decide
def Closure7C040rows : List (List GridPoint) := [row7_320,row7_321,row7_322,row7_323,row7_324,row7_325,row7_326,row7_327]
theorem Closure7C040_closed : ∀ row ∈ Closure7C040rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C040rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_320choice,row7_320_checked⟩
  · subst row
    exact ⟨row7_321choice,row7_321_checked⟩
  · subst row
    exact ⟨row7_322choice,row7_322_checked⟩
  · subst row
    exact ⟨row7_323choice,row7_323_checked⟩
  · subst row
    exact ⟨row7_324choice,row7_324_checked⟩
  · subst row
    exact ⟨row7_325choice,row7_325_checked⟩
  · subst row
    exact ⟨row7_326choice,row7_326_checked⟩
  · subst row
    exact ⟨row7_327choice,row7_327_checked⟩
end Polyomino57
