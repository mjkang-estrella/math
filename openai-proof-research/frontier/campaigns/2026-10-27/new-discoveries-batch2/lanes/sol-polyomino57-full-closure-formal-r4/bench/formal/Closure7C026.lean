import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_208 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0)]
def row7_208choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1001,(1,0))),((-1,1),(1667,(1,0))),((0,-1),(370,(0,1))),((0,2),(308,(0,0))),((1,0),(472,(0,0))),((1,2),(585,(0,0))),((2,0),(632,(0,0))),((2,2),(656,(0,0))),((3,-1),(1414,(0,1))),((3,2),(672,(0,0))),((4,-1),(1416,(0,1))),((4,1),(675,(0,0))),((5,0),(676,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_208_checked : successorFastRowCheck layer8 row7_208 row7_208choice = true := by decide
def row7_209 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1)]
def row7_209choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1002,(1,0))),((-1,1),(1668,(1,0))),((0,-1),(371,(0,1))),((0,2),(309,(0,0))),((1,0),(473,(0,0))),((1,2),(586,(0,0))),((2,0),(633,(0,0))),((2,2),(657,(0,0))),((3,-1),(1415,(0,1))),((3,2),(673,(0,0))),((4,0),(675,(0,0))),((4,2),(677,(0,0))),((5,1),(678,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_209_checked : successorFastRowCheck layer8 row7_209 row7_209choice = true := by decide
def row7_210 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3)]
def row7_210choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1003,(1,0))),((-1,1),(1669,(1,0))),((0,-1),(372,(0,1))),((0,2),(310,(0,0))),((1,0),(474,(0,0))),((1,2),(587,(0,0))),((2,0),(636,(0,0))),((2,2),(658,(0,0))),((2,3),(670,(0,0))),((3,0),(671,(0,0))),((3,4),(679,(0,0))),((4,1),(680,(0,0))),((4,2),(681,(0,0))),((4,3),(682,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_210_checked : successorFastRowCheck layer8 row7_210 row7_210choice = true := by decide
def row7_211 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1)]
def row7_211choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1004,(1,0))),((-1,1),(1670,(1,0))),((0,-1),(373,(0,1))),((0,2),(311,(0,0))),((1,0),(475,(0,0))),((1,2),(588,(0,0))),((2,0),(637,(0,0))),((2,2),(659,(0,0))),((3,0),(673,(0,0))),((3,3),(680,(0,0))),((4,0),(683,(0,0))),((4,2),(684,(0,0))),((5,1),(685,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_211_checked : successorFastRowCheck layer8 row7_211 row7_211choice = true := by decide
def row7_212 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2)]
def row7_212choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1005,(1,0))),((-1,1),(1671,(1,0))),((0,-1),(374,(0,1))),((0,2),(312,(0,0))),((1,0),(476,(0,0))),((1,2),(589,(0,0))),((2,0),(638,(0,0))),((2,2),(660,(0,0))),((3,0),(674,(0,0))),((3,3),(681,(0,0))),((4,1),(684,(0,0))),((4,3),(686,(0,0))),((5,2),(687,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_212_checked : successorFastRowCheck layer8 row7_212 row7_212choice = true := by decide
def row7_213 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1)]
def row7_213choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1006,(1,0))),((-1,1),(1672,(1,0))),((0,-1),(375,(0,1))),((0,2),(313,(0,0))),((1,0),(477,(0,0))),((1,2),(590,(0,0))),((2,0),(639,(0,0))),((2,2),(661,(0,0))),((3,0),(675,(0,0))),((3,2),(683,(0,0))),((4,-1),(1417,(0,1))),((4,2),(688,(0,0))),((5,0),(689,(0,0))),((5,1),(690,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_213_checked : successorFastRowCheck layer8 row7_213 row7_213choice = true := by decide
def row7_214 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2)]
def row7_214choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1007,(1,0))),((-1,1),(1673,(1,0))),((0,-1),(376,(0,1))),((0,2),(314,(0,0))),((1,0),(478,(0,0))),((1,2),(591,(0,0))),((2,0),(640,(0,0))),((2,2),(662,(0,0))),((3,0),(677,(0,0))),((3,2),(684,(0,0))),((4,0),(688,(0,0))),((4,3),(691,(0,0))),((5,1),(692,(0,0))),((5,2),(693,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_214_checked : successorFastRowCheck layer8 row7_214 row7_214choice = true := by decide
def row7_215 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1)]
def row7_215choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1008,(1,0))),((-1,1),(1674,(1,0))),((0,-1),(377,(0,1))),((0,2),(315,(0,0))),((1,0),(479,(0,0))),((1,2),(592,(0,0))),((2,0),(641,(0,0))),((2,2),(663,(0,0))),((3,0),(678,(0,0))),((3,2),(685,(0,0))),((4,0),(690,(0,0))),((4,2),(692,(0,0))),((5,0),(694,(0,0))),((5,2),(695,(0,0))),((6,1),(696,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_215_checked : successorFastRowCheck layer8 row7_215 row7_215choice = true := by decide
def Closure7C026rows : List (List GridPoint) := [row7_208,row7_209,row7_210,row7_211,row7_212,row7_213,row7_214,row7_215]
theorem Closure7C026_closed : ∀ row ∈ Closure7C026rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C026rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_208choice,row7_208_checked⟩
  · subst row
    exact ⟨row7_209choice,row7_209_checked⟩
  · subst row
    exact ⟨row7_210choice,row7_210_checked⟩
  · subst row
    exact ⟨row7_211choice,row7_211_checked⟩
  · subst row
    exact ⟨row7_212choice,row7_212_checked⟩
  · subst row
    exact ⟨row7_213choice,row7_213_checked⟩
  · subst row
    exact ⟨row7_214choice,row7_214_checked⟩
  · subst row
    exact ⟨row7_215choice,row7_215_checked⟩
end Polyomino57
