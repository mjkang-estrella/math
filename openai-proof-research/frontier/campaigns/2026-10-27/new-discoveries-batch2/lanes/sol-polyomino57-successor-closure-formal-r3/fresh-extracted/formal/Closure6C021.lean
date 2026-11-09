import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_168 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(4,1)]
def row6_168choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(561,(1,0))),((0,0),(197,(0,0))),((0,2),(415,(0,0))),((1,0),(481,(0,0))),((1,2),(518,(0,0))),((2,-1),(682,(0,1))),((2,2),(535,(0,0))),((3,0),(540,(0,0))),((3,2),(544,(0,0))),((4,0),(546,(0,0))),((4,2),(547,(0,0))),((5,1),(548,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_168_checked : successorFastRowCheck layer7 row6_168 row6_168choice = true := by decide
def row6_169 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1)]
def row6_169choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(562,(1,0))),((0,0),(202,(0,0))),((0,2),(416,(0,0))),((1,0),(491,(0,0))),((1,2),(519,(0,0))),((2,0),(531,(0,0))),((2,3),(549,(0,0))),((3,-1),(689,(0,1))),((3,2),(550,(0,0))),((4,0),(551,(0,0))),((4,1),(552,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_169_checked : successorFastRowCheck layer7 row6_169 row6_169choice = true := by decide
def row6_170 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2)]
def row6_170choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(563,(1,0))),((0,0),(207,(0,0))),((0,2),(417,(0,0))),((1,0),(496,(0,0))),((1,2),(520,(0,0))),((2,0),(538,(0,0))),((2,2),(550,(0,0))),((3,-1),(690,(0,1))),((3,3),(554,(0,0))),((4,0),(555,(0,0))),((4,1),(556,(0,0))),((4,2),(557,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_170_checked : successorFastRowCheck layer7 row6_170 row6_170choice = true := by decide
def row6_171 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0)]
def row6_171choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(564,(1,0))),((0,0),(208,(0,0))),((0,2),(418,(0,0))),((1,0),(497,(0,0))),((1,2),(521,(0,0))),((2,0),(539,(0,0))),((2,2),(551,(0,0))),((3,-1),(692,(0,1))),((3,2),(555,(0,0))),((4,-1),(694,(0,1))),((4,1),(558,(0,0))),((5,0),(559,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_171_checked : successorFastRowCheck layer7 row6_171 row6_171choice = true := by decide
def row6_172 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1)]
def row6_172choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(565,(1,0))),((0,0),(209,(0,0))),((0,2),(419,(0,0))),((1,0),(498,(0,0))),((1,2),(522,(0,0))),((2,0),(540,(0,0))),((2,2),(552,(0,0))),((3,-1),(693,(0,1))),((3,2),(556,(0,0))),((4,0),(558,(0,0))),((4,2),(560,(0,0))),((5,1),(561,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_172_checked : successorFastRowCheck layer7 row6_172 row6_172choice = true := by decide
def row6_173 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1)]
def row6_173choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(566,(1,0))),((0,0),(213,(0,0))),((0,2),(420,(0,0))),((1,0),(502,(0,0))),((1,2),(523,(0,0))),((2,0),(546,(0,0))),((2,2),(553,(0,0))),((3,0),(558,(0,0))),((3,2),(562,(0,0))),((4,-1),(695,(0,1))),((4,2),(563,(0,0))),((5,0),(564,(0,0))),((5,1),(565,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_173_checked : successorFastRowCheck layer7 row6_173 row6_173choice = true := by decide
def row6_174 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)]
def row6_174choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(664,(1,0))),((-1,3),(732,(1,0))),((-1,4),(756,(1,0))),((0,0),(216,(0,0))),((0,1),(354,(0,0))),((0,5),(567,(0,0))),((1,-1),(696,(0,1))),((1,3),(568,(0,0))),((1,4),(569,(0,0))),((2,0),(570,(0,0))),((2,1),(571,(0,0))),((2,2),(572,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_174_checked : successorFastRowCheck layer7 row6_174 row6_174choice = true := by decide
def row6_175 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]
def row6_175choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(665,(1,0))),((-1,3),(733,(1,0))),((0,0),(217,(0,0))),((0,1),(360,(0,0))),((0,4),(568,(0,0))),((1,-1),(697,(0,1))),((1,4),(575,(0,0))),((2,0),(576,(0,0))),((2,1),(577,(0,0))),((2,2),(578,(0,0))),((2,3),(579,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_175_checked : successorFastRowCheck layer7 row6_175 row6_175choice = true := by decide
def Closure6C021rows : List (List GridPoint) := [row6_168,row6_169,row6_170,row6_171,row6_172,row6_173,row6_174,row6_175]
theorem Closure6C021_closed : ∀ row ∈ Closure6C021rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C021rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_168choice,row6_168_checked⟩
  · subst row
    exact ⟨row6_169choice,row6_169_checked⟩
  · subst row
    exact ⟨row6_170choice,row6_170_checked⟩
  · subst row
    exact ⟨row6_171choice,row6_171_checked⟩
  · subst row
    exact ⟨row6_172choice,row6_172_checked⟩
  · subst row
    exact ⟨row6_173choice,row6_173_checked⟩
  · subst row
    exact ⟨row6_174choice,row6_174_checked⟩
  · subst row
    exact ⟨row6_175choice,row6_175_checked⟩
end Polyomino57
