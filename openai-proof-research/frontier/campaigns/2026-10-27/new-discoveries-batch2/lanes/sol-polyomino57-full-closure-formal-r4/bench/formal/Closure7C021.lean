import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_168 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3)]
def row7_168choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(961,(1,0))),((-1,1),(1627,(1,0))),((0,-1),(323,(0,1))),((0,2),(268,(0,0))),((0,3),(396,(0,0))),((1,0),(422,(0,0))),((1,4),(531,(0,0))),((2,0),(542,(0,0))),((2,2),(545,(0,0))),((2,4),(548,(0,0))),((3,1),(549,(0,0))),((3,3),(550,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_168_checked : successorFastRowCheck layer8 row7_168 row7_168choice = true := by decide
def row7_169 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1)]
def row7_169choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(962,(1,0))),((-1,1),(1628,(1,0))),((0,-1),(324,(0,1))),((0,2),(269,(0,0))),((0,3),(397,(0,0))),((1,0),(423,(0,0))),((1,4),(533,(0,0))),((2,0),(544,(0,0))),((2,2),(546,(0,0))),((2,3),(549,(0,0))),((3,0),(551,(0,0))),((3,2),(552,(0,0))),((4,1),(553,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_169_checked : successorFastRowCheck layer8 row7_169 row7_169choice = true := by decide
def row7_170 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3)]
def row7_170choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(963,(1,0))),((-1,1),(1629,(1,0))),((0,-1),(325,(0,1))),((0,2),(270,(0,0))),((0,3),(398,(0,0))),((1,0),(424,(0,0))),((1,4),(534,(0,0))),((2,1),(545,(0,0))),((2,4),(554,(0,0))),((3,2),(555,(0,0))),((3,3),(556,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_170_checked : successorFastRowCheck layer8 row7_170 row7_170choice = true := by decide
def row7_171 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2)]
def row7_171choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(964,(1,0))),((-1,1),(1630,(1,0))),((0,-1),(326,(0,1))),((0,2),(271,(0,0))),((0,3),(399,(0,0))),((1,0),(425,(0,0))),((1,4),(536,(0,0))),((2,1),(547,(0,0))),((2,3),(555,(0,0))),((3,1),(557,(0,0))),((3,3),(558,(0,0))),((4,2),(559,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_171_checked : successorFastRowCheck layer8 row7_171 row7_171choice = true := by decide
def row7_172 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4)]
def row7_172choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(965,(1,0))),((-1,1),(1631,(1,0))),((0,-1),(327,(0,1))),((0,2),(272,(0,0))),((0,3),(400,(0,0))),((1,0),(426,(0,0))),((1,4),(537,(0,0))),((2,1),(548,(0,0))),((2,2),(554,(0,0))),((2,5),(560,(0,0))),((3,3),(561,(0,0))),((3,4),(562,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_172_checked : successorFastRowCheck layer8 row7_172 row7_172choice = true := by decide
def row7_173 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3)]
def row7_173choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(966,(1,0))),((-1,1),(1632,(1,0))),((0,-1),(328,(0,1))),((0,2),(273,(0,0))),((0,3),(401,(0,0))),((1,0),(427,(0,0))),((1,4),(538,(0,0))),((2,1),(550,(0,0))),((2,2),(556,(0,0))),((2,4),(561,(0,0))),((3,2),(563,(0,0))),((3,4),(564,(0,0))),((4,3),(565,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_173_checked : successorFastRowCheck layer8 row7_173 row7_173choice = true := by decide
def row7_174 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2)]
def row7_174choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(967,(1,0))),((-1,1),(1633,(1,0))),((0,-1),(330,(0,1))),((0,2),(274,(0,0))),((1,0),(428,(0,0))),((1,3),(541,(0,0))),((2,-1),(1387,(0,1))),((2,3),(567,(0,0))),((3,0),(568,(0,0))),((3,1),(569,(0,0))),((3,2),(570,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_174_checked : successorFastRowCheck layer8 row7_174 row7_174choice = true := by decide
def row7_175 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0)]
def row7_175choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(968,(1,0))),((-1,1),(1634,(1,0))),((0,-1),(331,(0,1))),((0,2),(275,(0,0))),((1,0),(429,(0,0))),((1,3),(543,(0,0))),((2,-1),(1389,(0,1))),((2,2),(568,(0,0))),((3,-1),(1391,(0,1))),((3,1),(571,(0,0))),((4,0),(572,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_175_checked : successorFastRowCheck layer8 row7_175 row7_175choice = true := by decide
def Closure7C021rows : List (List GridPoint) := [row7_168,row7_169,row7_170,row7_171,row7_172,row7_173,row7_174,row7_175]
theorem Closure7C021_closed : ∀ row ∈ Closure7C021rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C021rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_168choice,row7_168_checked⟩
  · subst row
    exact ⟨row7_169choice,row7_169_checked⟩
  · subst row
    exact ⟨row7_170choice,row7_170_checked⟩
  · subst row
    exact ⟨row7_171choice,row7_171_checked⟩
  · subst row
    exact ⟨row7_172choice,row7_172_checked⟩
  · subst row
    exact ⟨row7_173choice,row7_173_checked⟩
  · subst row
    exact ⟨row7_174choice,row7_174_checked⟩
  · subst row
    exact ⟨row7_175choice,row7_175_checked⟩
end Polyomino57
