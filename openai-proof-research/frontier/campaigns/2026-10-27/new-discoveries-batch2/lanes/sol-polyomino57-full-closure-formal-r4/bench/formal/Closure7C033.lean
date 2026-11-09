import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_264 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)]
def row7_264choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1057,(1,0))),((0,-1),(552,(0,1))),((0,1),(434,(0,0))),((0,2),(740,(0,0))),((1,-1),(1501,(0,1))),((1,3),(826,(0,0))),((2,-1),(1692,(0,1))),((2,1),(854,(0,0))),((2,2),(862,(0,0))),((3,-1),(1696,(0,1))),((3,2),(868,(0,0))),((4,0),(869,(0,0))),((4,1),(870,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_264_checked : successorFastRowCheck layer8 row7_264 row7_264choice = true := by decide
def row7_265 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]
def row7_265choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1058,(1,0))),((0,-1),(553,(0,1))),((0,1),(435,(0,0))),((0,2),(741,(0,0))),((1,-1),(1502,(0,1))),((1,3),(827,(0,0))),((2,-1),(1693,(0,1))),((2,1),(855,(0,0))),((2,2),(864,(0,0))),((3,-1),(1698,(0,1))),((3,1),(869,(0,0))),((4,-1),(1699,(0,1))),((4,1),(871,(0,0))),((5,0),(872,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_265_checked : successorFastRowCheck layer8 row7_265 row7_265choice = true := by decide
def row7_266 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)]
def row7_266choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1059,(1,0))),((0,-1),(554,(0,1))),((0,1),(436,(0,0))),((0,2),(742,(0,0))),((1,-1),(1503,(0,1))),((1,3),(828,(0,0))),((2,0),(850,(0,0))),((2,4),(873,(0,0))),((3,1),(874,(0,0))),((3,2),(875,(0,0))),((3,3),(876,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_266_checked : successorFastRowCheck layer8 row7_266 row7_266choice = true := by decide
def row7_267 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)]
def row7_267choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1060,(1,0))),((0,-1),(555,(0,1))),((0,1),(437,(0,0))),((0,2),(743,(0,0))),((1,-1),(1504,(0,1))),((1,3),(829,(0,0))),((2,0),(852,(0,0))),((2,3),(874,(0,0))),((3,0),(877,(0,0))),((3,2),(878,(0,0))),((4,1),(879,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_267_checked : successorFastRowCheck layer8 row7_267 row7_267choice = true := by decide
def row7_268 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]
def row7_268choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1061,(1,0))),((0,-1),(556,(0,1))),((0,1),(438,(0,0))),((0,2),(744,(0,0))),((1,-1),(1505,(0,1))),((1,3),(830,(0,0))),((2,0),(853,(0,0))),((2,3),(875,(0,0))),((3,1),(878,(0,0))),((3,3),(880,(0,0))),((4,2),(881,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_268_checked : successorFastRowCheck layer8 row7_268 row7_268choice = true := by decide
def row7_269 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)]
def row7_269choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1062,(1,0))),((0,-1),(557,(0,1))),((0,1),(439,(0,0))),((0,2),(745,(0,0))),((1,-1),(1506,(0,1))),((1,3),(834,(0,0))),((2,0),(854,(0,0))),((2,2),(877,(0,0))),((3,-1),(1700,(0,1))),((3,2),(882,(0,0))),((4,0),(883,(0,0))),((4,1),(884,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_269_checked : successorFastRowCheck layer8 row7_269 row7_269choice = true := by decide
def row7_270 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)]
def row7_270choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1063,(1,0))),((0,-1),(558,(0,1))),((0,1),(440,(0,0))),((0,2),(746,(0,0))),((1,-1),(1507,(0,1))),((1,3),(835,(0,0))),((2,0),(856,(0,0))),((2,2),(878,(0,0))),((3,0),(882,(0,0))),((3,3),(885,(0,0))),((4,1),(886,(0,0))),((4,2),(887,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_270_checked : successorFastRowCheck layer8 row7_270 row7_270choice = true := by decide
def row7_271 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]
def row7_271choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1064,(1,0))),((0,-1),(559,(0,1))),((0,1),(441,(0,0))),((0,2),(747,(0,0))),((1,-1),(1508,(0,1))),((1,3),(836,(0,0))),((2,0),(857,(0,0))),((2,2),(879,(0,0))),((3,0),(884,(0,0))),((3,2),(886,(0,0))),((4,0),(888,(0,0))),((4,2),(889,(0,0))),((5,1),(890,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_271_checked : successorFastRowCheck layer8 row7_271 row7_271choice = true := by decide
def Closure7C033rows : List (List GridPoint) := [row7_264,row7_265,row7_266,row7_267,row7_268,row7_269,row7_270,row7_271]
theorem Closure7C033_closed : ∀ row ∈ Closure7C033rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C033rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_264choice,row7_264_checked⟩
  · subst row
    exact ⟨row7_265choice,row7_265_checked⟩
  · subst row
    exact ⟨row7_266choice,row7_266_checked⟩
  · subst row
    exact ⟨row7_267choice,row7_267_checked⟩
  · subst row
    exact ⟨row7_268choice,row7_268_checked⟩
  · subst row
    exact ⟨row7_269choice,row7_269_checked⟩
  · subst row
    exact ⟨row7_270choice,row7_270_checked⟩
  · subst row
    exact ⟨row7_271choice,row7_271_checked⟩
end Polyomino57
