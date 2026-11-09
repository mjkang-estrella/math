import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_88 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0)]
def row6_88choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(329,(1,0))),((0,-1),(178,(0,1))),((0,1),(137,(0,0))),((1,-1),(462,(0,1))),((1,2),(259,(0,0))),((2,-1),(513,(0,1))),((2,2),(280,(0,0))),((3,-1),(519,(0,1))),((3,1),(283,(0,0))),((4,0),(284,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_88_checked : successorFastRowCheck layer7 row6_88 row6_88choice = true := by decide
def row6_89 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1)]
def row6_89choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(330,(1,0))),((0,-1),(179,(0,1))),((0,1),(138,(0,0))),((1,-1),(463,(0,1))),((1,2),(260,(0,0))),((2,-1),(514,(0,1))),((2,2),(281,(0,0))),((3,0),(283,(0,0))),((3,2),(285,(0,0))),((4,1),(286,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_89_checked : successorFastRowCheck layer7 row6_89 row6_89choice = true := by decide
def row6_90 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1)]
def row6_90choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(331,(1,0))),((0,-1),(181,(0,1))),((0,1),(139,(0,0))),((1,-1),(465,(0,1))),((1,2),(264,(0,0))),((2,-1),(517,(0,1))),((2,1),(283,(0,0))),((3,-1),(520,(0,1))),((3,2),(287,(0,0))),((4,0),(288,(0,0))),((4,1),(289,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_90_checked : successorFastRowCheck layer7 row6_90 row6_90choice = true := by decide
def row6_91 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0)]
def row6_91choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(332,(1,0))),((0,-1),(182,(0,1))),((0,1),(140,(0,0))),((1,-1),(466,(0,1))),((1,2),(265,(0,0))),((2,-1),(518,(0,1))),((2,1),(284,(0,0))),((3,-1),(522,(0,1))),((3,1),(288,(0,0))),((4,-1),(523,(0,1))),((4,1),(290,(0,0))),((5,0),(291,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_91_checked : successorFastRowCheck layer7 row6_91 row6_91choice = true := by decide
def row6_92 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3)]
def row6_92choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(333,(1,0))),((0,-1),(183,(0,1))),((0,1),(141,(0,0))),((1,-1),(467,(0,1))),((1,2),(266,(0,0))),((1,3),(278,(0,0))),((2,0),(279,(0,0))),((2,4),(292,(0,0))),((3,1),(293,(0,0))),((3,2),(294,(0,0))),((3,3),(295,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_92_checked : successorFastRowCheck layer7 row6_92 row6_92choice = true := by decide
def row6_93 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1)]
def row6_93choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(334,(1,0))),((0,-1),(184,(0,1))),((0,1),(142,(0,0))),((1,-1),(468,(0,1))),((1,2),(267,(0,0))),((2,0),(281,(0,0))),((2,3),(293,(0,0))),((3,0),(296,(0,0))),((3,2),(297,(0,0))),((4,1),(298,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_93_checked : successorFastRowCheck layer7 row6_93 row6_93choice = true := by decide
def row6_94 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2)]
def row6_94choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(335,(1,0))),((0,-1),(185,(0,1))),((0,1),(143,(0,0))),((1,-1),(469,(0,1))),((1,2),(268,(0,0))),((2,0),(282,(0,0))),((2,3),(294,(0,0))),((3,1),(297,(0,0))),((3,3),(299,(0,0))),((4,2),(300,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_94_checked : successorFastRowCheck layer7 row6_94 row6_94choice = true := by decide
def row6_95 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1)]
def row6_95choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(336,(1,0))),((0,-1),(186,(0,1))),((0,1),(144,(0,0))),((1,-1),(470,(0,1))),((1,2),(269,(0,0))),((2,0),(283,(0,0))),((2,2),(296,(0,0))),((3,-1),(524,(0,1))),((3,2),(301,(0,0))),((4,0),(302,(0,0))),((4,1),(303,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_95_checked : successorFastRowCheck layer7 row6_95 row6_95choice = true := by decide
def Closure6C011rows : List (List GridPoint) := [row6_88,row6_89,row6_90,row6_91,row6_92,row6_93,row6_94,row6_95]
theorem Closure6C011_closed : ∀ row ∈ Closure6C011rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C011rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_88choice,row6_88_checked⟩
  · subst row
    exact ⟨row6_89choice,row6_89_checked⟩
  · subst row
    exact ⟨row6_90choice,row6_90_checked⟩
  · subst row
    exact ⟨row6_91choice,row6_91_checked⟩
  · subst row
    exact ⟨row6_92choice,row6_92_checked⟩
  · subst row
    exact ⟨row6_93choice,row6_93_checked⟩
  · subst row
    exact ⟨row6_94choice,row6_94_checked⟩
  · subst row
    exact ⟨row6_95choice,row6_95_checked⟩
end Polyomino57
