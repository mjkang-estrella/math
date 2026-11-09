import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_200 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2)]
def row7_200choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(993,(1,0))),((-1,1),(1659,(1,0))),((0,-1),(361,(0,1))),((0,2),(300,(0,0))),((1,0),(464,(0,0))),((1,2),(577,(0,0))),((1,3),(616,(0,0))),((2,0),(622,(0,0))),((2,4),(644,(0,0))),((3,1),(648,(0,0))),((3,3),(651,(0,0))),((4,2),(652,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_200_checked : successorFastRowCheck layer8 row7_200 row7_200choice = true := by decide
def row7_201 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3)]
def row7_201choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(994,(1,0))),((-1,1),(1660,(1,0))),((0,-1),(362,(0,1))),((0,2),(301,(0,0))),((1,0),(465,(0,0))),((1,2),(578,(0,0))),((1,3),(617,(0,0))),((2,0),(623,(0,0))),((2,4),(645,(0,0))),((3,1),(649,(0,0))),((3,2),(651,(0,0))),((3,4),(653,(0,0))),((4,3),(654,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_201_checked : successorFastRowCheck layer8 row7_201 row7_201choice = true := by decide
def row7_202 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1)]
def row7_202choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(995,(1,0))),((-1,1),(1661,(1,0))),((0,-1),(363,(0,1))),((0,2),(302,(0,0))),((1,0),(466,(0,0))),((1,2),(579,(0,0))),((2,0),(624,(0,0))),((2,3),(647,(0,0))),((3,-1),(1411,(0,1))),((3,2),(655,(0,0))),((4,0),(656,(0,0))),((4,1),(657,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_202_checked : successorFastRowCheck layer8 row7_202 row7_202choice = true := by decide
def row7_203 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2)]
def row7_203choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(996,(1,0))),((-1,1),(1662,(1,0))),((0,-1),(364,(0,1))),((0,2),(303,(0,0))),((1,0),(467,(0,0))),((1,2),(580,(0,0))),((2,0),(627,(0,0))),((2,3),(648,(0,0))),((3,0),(655,(0,0))),((3,3),(658,(0,0))),((4,1),(659,(0,0))),((4,2),(660,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_203_checked : successorFastRowCheck layer8 row7_203 row7_203choice = true := by decide
def row7_204 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1)]
def row7_204choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(997,(1,0))),((-1,1),(1663,(1,0))),((0,-1),(365,(0,1))),((0,2),(304,(0,0))),((1,0),(468,(0,0))),((1,2),(581,(0,0))),((2,0),(628,(0,0))),((2,3),(650,(0,0))),((3,0),(657,(0,0))),((3,2),(659,(0,0))),((4,0),(661,(0,0))),((4,2),(662,(0,0))),((5,1),(663,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_204_checked : successorFastRowCheck layer8 row7_204 row7_204choice = true := by decide
def row7_205 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3)]
def row7_205choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(998,(1,0))),((-1,1),(1664,(1,0))),((0,-1),(366,(0,1))),((0,2),(305,(0,0))),((1,0),(469,(0,0))),((1,2),(582,(0,0))),((2,0),(629,(0,0))),((2,3),(651,(0,0))),((3,1),(658,(0,0))),((3,4),(664,(0,0))),((4,2),(665,(0,0))),((4,3),(666,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_205_checked : successorFastRowCheck layer8 row7_205 row7_205choice = true := by decide
def row7_206 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2)]
def row7_206choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(999,(1,0))),((-1,1),(1665,(1,0))),((0,-1),(367,(0,1))),((0,2),(306,(0,0))),((1,0),(470,(0,0))),((1,2),(583,(0,0))),((2,0),(630,(0,0))),((2,3),(652,(0,0))),((3,1),(660,(0,0))),((3,3),(665,(0,0))),((4,1),(667,(0,0))),((4,3),(668,(0,0))),((5,2),(669,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_206_checked : successorFastRowCheck layer8 row7_206 row7_206choice = true := by decide
def row7_207 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2)]
def row7_207choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1000,(1,0))),((-1,1),(1666,(1,0))),((0,-1),(369,(0,1))),((0,2),(307,(0,0))),((1,0),(471,(0,0))),((1,2),(584,(0,0))),((2,0),(631,(0,0))),((2,2),(655,(0,0))),((3,-1),(1412,(0,1))),((3,3),(671,(0,0))),((4,0),(672,(0,0))),((4,1),(673,(0,0))),((4,2),(674,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_207_checked : successorFastRowCheck layer8 row7_207 row7_207choice = true := by decide
def Closure7C025rows : List (List GridPoint) := [row7_200,row7_201,row7_202,row7_203,row7_204,row7_205,row7_206,row7_207]
theorem Closure7C025_closed : ∀ row ∈ Closure7C025rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C025rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_200choice,row7_200_checked⟩
  · subst row
    exact ⟨row7_201choice,row7_201_checked⟩
  · subst row
    exact ⟨row7_202choice,row7_202_checked⟩
  · subst row
    exact ⟨row7_203choice,row7_203_checked⟩
  · subst row
    exact ⟨row7_204choice,row7_204_checked⟩
  · subst row
    exact ⟨row7_205choice,row7_205_checked⟩
  · subst row
    exact ⟨row7_206choice,row7_206_checked⟩
  · subst row
    exact ⟨row7_207choice,row7_207_checked⟩
end Polyomino57
