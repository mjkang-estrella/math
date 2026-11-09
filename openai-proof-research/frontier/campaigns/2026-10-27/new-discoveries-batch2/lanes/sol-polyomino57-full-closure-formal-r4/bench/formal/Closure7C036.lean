import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_288 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)]
def row7_288choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1081,(1,0))),((0,-1),(588,(0,1))),((0,1),(458,(0,0))),((1,-1),(1552,(0,1))),((1,2),(869,(0,0))),((2,-1),(1719,(0,1))),((2,1),(930,(0,0))),((3,-1),(1732,(0,1))),((3,2),(942,(0,0))),((4,-1),(1738,(0,1))),((4,1),(945,(0,0))),((5,0),(946,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_288_checked : successorFastRowCheck layer8 row7_288 row7_288choice = true := by decide
def row7_289 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]
def row7_289choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1082,(1,0))),((0,-1),(589,(0,1))),((0,1),(459,(0,0))),((1,-1),(1553,(0,1))),((1,2),(870,(0,0))),((2,-1),(1720,(0,1))),((2,1),(931,(0,0))),((3,-1),(1733,(0,1))),((3,2),(943,(0,0))),((4,0),(945,(0,0))),((4,2),(947,(0,0))),((5,1),(948,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_289_checked : successorFastRowCheck layer8 row7_289 row7_289choice = true := by decide
def row7_290 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)]
def row7_290choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1083,(1,0))),((0,-1),(591,(0,1))),((0,1),(460,(0,0))),((1,-1),(1555,(0,1))),((1,2),(871,(0,0))),((2,-1),(1722,(0,1))),((2,1),(932,(0,0))),((3,-1),(1736,(0,1))),((3,1),(945,(0,0))),((4,-1),(1739,(0,1))),((4,2),(949,(0,0))),((5,0),(950,(0,0))),((5,1),(951,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_290_checked : successorFastRowCheck layer8 row7_290 row7_290choice = true := by decide
def row7_291 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]
def row7_291choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1084,(1,0))),((0,-1),(592,(0,1))),((0,1),(461,(0,0))),((1,-1),(1556,(0,1))),((1,2),(872,(0,0))),((2,-1),(1723,(0,1))),((2,1),(933,(0,0))),((3,-1),(1737,(0,1))),((3,1),(946,(0,0))),((4,-1),(1741,(0,1))),((4,1),(950,(0,0))),((5,-1),(1742,(0,1))),((5,1),(952,(0,0))),((6,0),(953,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_291_checked : successorFastRowCheck layer8 row7_291 row7_291choice = true := by decide
def row7_292 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)]
def row7_292choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1085,(1,0))),((0,-1),(593,(0,1))),((0,1),(462,(0,0))),((1,-1),(1557,(0,1))),((1,2),(873,(0,0))),((1,3),(912,(0,0))),((1,4),(916,(0,0))),((2,0),(917,(0,0))),((2,5),(954,(0,0))),((3,1),(955,(0,0))),((3,2),(956,(0,0))),((3,3),(957,(0,0))),((3,4),(958,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_292_checked : successorFastRowCheck layer8 row7_292 row7_292choice = true := by decide
def row7_293 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)]
def row7_293choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1086,(1,0))),((0,-1),(594,(0,1))),((0,1),(463,(0,0))),((1,-1),(1558,(0,1))),((1,2),(874,(0,0))),((1,3),(913,(0,0))),((2,0),(919,(0,0))),((2,4),(955,(0,0))),((3,0),(959,(0,0))),((3,2),(960,(0,0))),((3,3),(961,(0,0))),((4,1),(962,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_293_checked : successorFastRowCheck layer8 row7_293 row7_293choice = true := by decide
def row7_294 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)]
def row7_294choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1087,(1,0))),((0,-1),(595,(0,1))),((0,1),(464,(0,0))),((1,-1),(1559,(0,1))),((1,2),(875,(0,0))),((1,3),(914,(0,0))),((2,0),(920,(0,0))),((2,4),(956,(0,0))),((3,1),(960,(0,0))),((3,3),(963,(0,0))),((4,2),(964,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_294_checked : successorFastRowCheck layer8 row7_294 row7_294choice = true := by decide
def row7_295 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]
def row7_295choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1088,(1,0))),((0,-1),(596,(0,1))),((0,1),(465,(0,0))),((1,-1),(1560,(0,1))),((1,2),(876,(0,0))),((1,3),(915,(0,0))),((2,0),(921,(0,0))),((2,4),(957,(0,0))),((3,1),(961,(0,0))),((3,2),(963,(0,0))),((3,4),(965,(0,0))),((4,3),(966,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_295_checked : successorFastRowCheck layer8 row7_295 row7_295choice = true := by decide
def Closure7C036rows : List (List GridPoint) := [row7_288,row7_289,row7_290,row7_291,row7_292,row7_293,row7_294,row7_295]
theorem Closure7C036_closed : ∀ row ∈ Closure7C036rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C036rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_288choice,row7_288_checked⟩
  · subst row
    exact ⟨row7_289choice,row7_289_checked⟩
  · subst row
    exact ⟨row7_290choice,row7_290_checked⟩
  · subst row
    exact ⟨row7_291choice,row7_291_checked⟩
  · subst row
    exact ⟨row7_292choice,row7_292_checked⟩
  · subst row
    exact ⟨row7_293choice,row7_293_checked⟩
  · subst row
    exact ⟨row7_294choice,row7_294_checked⟩
  · subst row
    exact ⟨row7_295choice,row7_295_checked⟩
end Polyomino57
