import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_136 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2)]
def row7_136choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(929,(1,0))),((-1,1),(1595,(1,0))),((0,-1),(277,(0,1))),((0,2),(206,(0,0))),((1,-1),(1275,(0,1))),((1,2),(428,(0,0))),((2,-1),(1330,(0,1))),((2,3),(449,(0,0))),((3,0),(450,(0,0))),((3,1),(451,(0,0))),((3,2),(452,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_136_checked : successorFastRowCheck layer8 row7_136 row7_136choice = true := by decide
def row7_137 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0)]
def row7_137choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(930,(1,0))),((-1,1),(1596,(1,0))),((0,-1),(278,(0,1))),((0,2),(207,(0,0))),((1,-1),(1276,(0,1))),((1,2),(429,(0,0))),((2,-1),(1332,(0,1))),((2,2),(450,(0,0))),((3,-1),(1338,(0,1))),((3,1),(453,(0,0))),((4,0),(454,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_137_checked : successorFastRowCheck layer8 row7_137 row7_137choice = true := by decide
def row7_138 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1)]
def row7_138choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(931,(1,0))),((-1,1),(1597,(1,0))),((0,-1),(279,(0,1))),((0,2),(208,(0,0))),((1,-1),(1277,(0,1))),((1,2),(430,(0,0))),((2,-1),(1333,(0,1))),((2,2),(451,(0,0))),((3,0),(453,(0,0))),((3,2),(455,(0,0))),((4,1),(456,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_138_checked : successorFastRowCheck layer8 row7_138 row7_138choice = true := by decide
def row7_139 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1)]
def row7_139choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(932,(1,0))),((-1,1),(1598,(1,0))),((0,-1),(281,(0,1))),((0,2),(209,(0,0))),((1,-1),(1279,(0,1))),((1,2),(434,(0,0))),((2,-1),(1336,(0,1))),((2,1),(453,(0,0))),((3,-1),(1339,(0,1))),((3,2),(457,(0,0))),((4,0),(458,(0,0))),((4,1),(459,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_139_checked : successorFastRowCheck layer8 row7_139 row7_139choice = true := by decide
def row7_140 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0)]
def row7_140choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(933,(1,0))),((-1,1),(1599,(1,0))),((0,-1),(282,(0,1))),((0,2),(210,(0,0))),((1,-1),(1280,(0,1))),((1,2),(435,(0,0))),((2,-1),(1337,(0,1))),((2,1),(454,(0,0))),((3,-1),(1341,(0,1))),((3,1),(458,(0,0))),((4,-1),(1342,(0,1))),((4,1),(460,(0,0))),((5,0),(461,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_140_checked : successorFastRowCheck layer8 row7_140 row7_140choice = true := by decide
def row7_141 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3)]
def row7_141choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(934,(1,0))),((-1,1),(1600,(1,0))),((0,-1),(283,(0,1))),((0,2),(211,(0,0))),((1,-1),(1281,(0,1))),((1,2),(436,(0,0))),((1,3),(448,(0,0))),((2,0),(449,(0,0))),((2,4),(462,(0,0))),((3,1),(463,(0,0))),((3,2),(464,(0,0))),((3,3),(465,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_141_checked : successorFastRowCheck layer8 row7_141 row7_141choice = true := by decide
def row7_142 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1)]
def row7_142choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(935,(1,0))),((-1,1),(1601,(1,0))),((0,-1),(284,(0,1))),((0,2),(212,(0,0))),((1,-1),(1282,(0,1))),((1,2),(437,(0,0))),((2,0),(451,(0,0))),((2,3),(463,(0,0))),((3,0),(466,(0,0))),((3,2),(467,(0,0))),((4,1),(468,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_142_checked : successorFastRowCheck layer8 row7_142 row7_142choice = true := by decide
def row7_143 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2)]
def row7_143choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(936,(1,0))),((-1,1),(1602,(1,0))),((0,-1),(285,(0,1))),((0,2),(213,(0,0))),((1,-1),(1283,(0,1))),((1,2),(438,(0,0))),((2,0),(452,(0,0))),((2,3),(464,(0,0))),((3,1),(467,(0,0))),((3,3),(469,(0,0))),((4,2),(470,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_143_checked : successorFastRowCheck layer8 row7_143 row7_143choice = true := by decide
def Closure7C017rows : List (List GridPoint) := [row7_136,row7_137,row7_138,row7_139,row7_140,row7_141,row7_142,row7_143]
theorem Closure7C017_closed : ∀ row ∈ Closure7C017rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C017rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_136choice,row7_136_checked⟩
  · subst row
    exact ⟨row7_137choice,row7_137_checked⟩
  · subst row
    exact ⟨row7_138choice,row7_138_checked⟩
  · subst row
    exact ⟨row7_139choice,row7_139_checked⟩
  · subst row
    exact ⟨row7_140choice,row7_140_checked⟩
  · subst row
    exact ⟨row7_141choice,row7_141_checked⟩
  · subst row
    exact ⟨row7_142choice,row7_142_checked⟩
  · subst row
    exact ⟨row7_143choice,row7_143_checked⟩
end Polyomino57
