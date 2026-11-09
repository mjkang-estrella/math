import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_136 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row6_136choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(529,(1,0))),((0,0),(127,(0,0))),((0,2),(382,(0,0))),((0,3),(432,(0,0))),((1,-1),(606,(0,1))),((1,4),(439,(0,0))),((2,0),(443,(0,0))),((2,1),(446,(0,0))),((2,3),(449,(0,0))),((3,2),(450,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_136_checked : successorFastRowCheck layer7 row6_136 row6_136choice = true := by decide
def row6_137 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row6_137choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(530,(1,0))),((0,0),(128,(0,0))),((0,2),(383,(0,0))),((0,3),(433,(0,0))),((1,-1),(607,(0,1))),((1,4),(440,(0,0))),((2,0),(444,(0,0))),((2,1),(447,(0,0))),((2,2),(449,(0,0))),((2,4),(451,(0,0))),((3,3),(452,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_137_checked : successorFastRowCheck layer7 row6_137 row6_137choice = true := by decide
def row6_138 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1)]
def row6_138choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(531,(1,0))),((0,0),(129,(0,0))),((0,2),(384,(0,0))),((1,-1),(612,(0,1))),((1,3),(442,(0,0))),((2,-1),(645,(0,1))),((2,2),(453,(0,0))),((3,0),(454,(0,0))),((3,1),(455,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_138_checked : successorFastRowCheck layer7 row6_138 row6_138choice = true := by decide
def row6_139 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2)]
def row6_139choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(532,(1,0))),((0,0),(130,(0,0))),((0,2),(385,(0,0))),((1,-1),(613,(0,1))),((1,3),(443,(0,0))),((2,-1),(646,(0,1))),((2,1),(453,(0,0))),((2,3),(456,(0,0))),((3,0),(457,(0,0))),((3,2),(458,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_139_checked : successorFastRowCheck layer7 row6_139 row6_139choice = true := by decide
def row6_140 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0)]
def row6_140choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(533,(1,0))),((0,0),(131,(0,0))),((0,2),(386,(0,0))),((1,-1),(614,(0,1))),((1,3),(445,(0,0))),((2,-1),(648,(0,1))),((2,1),(454,(0,0))),((2,2),(457,(0,0))),((3,-1),(649,(0,1))),((3,1),(459,(0,0))),((4,0),(460,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_140_checked : successorFastRowCheck layer7 row6_140 row6_140choice = true := by decide
def row6_141 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2)]
def row6_141choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(534,(1,0))),((0,0),(132,(0,0))),((0,2),(387,(0,0))),((1,-1),(615,(0,1))),((1,3),(446,(0,0))),((2,0),(453,(0,0))),((2,3),(461,(0,0))),((3,1),(462,(0,0))),((3,2),(463,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_141_checked : successorFastRowCheck layer7 row6_141 row6_141choice = true := by decide
def row6_142 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1)]
def row6_142choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(535,(1,0))),((0,0),(133,(0,0))),((0,2),(388,(0,0))),((1,-1),(616,(0,1))),((1,3),(448,(0,0))),((2,0),(455,(0,0))),((2,2),(462,(0,0))),((3,0),(464,(0,0))),((3,2),(465,(0,0))),((4,1),(466,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_142_checked : successorFastRowCheck layer7 row6_142 row6_142choice = true := by decide
def row6_143 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3)]
def row6_143choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(536,(1,0))),((0,0),(134,(0,0))),((0,2),(389,(0,0))),((1,-1),(617,(0,1))),((1,3),(449,(0,0))),((2,0),(456,(0,0))),((2,1),(461,(0,0))),((2,4),(467,(0,0))),((3,2),(468,(0,0))),((3,3),(469,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_143_checked : successorFastRowCheck layer7 row6_143 row6_143choice = true := by decide
def Closure6C017rows : List (List GridPoint) := [row6_136,row6_137,row6_138,row6_139,row6_140,row6_141,row6_142,row6_143]
theorem Closure6C017_closed : ∀ row ∈ Closure6C017rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C017rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_136choice,row6_136_checked⟩
  · subst row
    exact ⟨row6_137choice,row6_137_checked⟩
  · subst row
    exact ⟨row6_138choice,row6_138_checked⟩
  · subst row
    exact ⟨row6_139choice,row6_139_checked⟩
  · subst row
    exact ⟨row6_140choice,row6_140_checked⟩
  · subst row
    exact ⟨row6_141choice,row6_141_checked⟩
  · subst row
    exact ⟨row6_142choice,row6_142_checked⟩
  · subst row
    exact ⟨row6_143choice,row6_143_checked⟩
end Polyomino57
