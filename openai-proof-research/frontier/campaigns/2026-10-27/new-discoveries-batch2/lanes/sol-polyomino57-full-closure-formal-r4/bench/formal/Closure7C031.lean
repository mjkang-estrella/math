import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_248 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)]
def row7_248choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1041,(1,0))),((0,-1),(531,(0,1))),((0,1),(418,(0,0))),((0,2),(724,(0,0))),((0,3),(772,(0,0))),((1,-1),(1472,(0,1))),((1,4),(801,(0,0))),((2,-1),(1677,(0,1))),((2,1),(816,(0,0))),((2,3),(820,(0,0))),((3,0),(821,(0,0))),((3,2),(822,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_248_checked : successorFastRowCheck layer8 row7_248 row7_248choice = true := by decide
def row7_249 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)]
def row7_249choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1042,(1,0))),((0,-1),(532,(0,1))),((0,1),(419,(0,0))),((0,2),(725,(0,0))),((0,3),(773,(0,0))),((1,-1),(1473,(0,1))),((1,4),(802,(0,0))),((2,-1),(1678,(0,1))),((2,1),(817,(0,0))),((2,2),(820,(0,0))),((2,4),(823,(0,0))),((3,0),(824,(0,0))),((3,3),(825,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_249_checked : successorFastRowCheck layer8 row7_249 row7_249choice = true := by decide
def row7_250 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]
def row7_250choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1043,(1,0))),((0,-1),(533,(0,1))),((0,1),(420,(0,0))),((0,2),(726,(0,0))),((0,3),(774,(0,0))),((1,-1),(1474,(0,1))),((1,4),(804,(0,0))),((2,-1),(1680,(0,1))),((2,1),(818,(0,0))),((2,2),(821,(0,0))),((2,3),(824,(0,0))),((3,-1),(1681,(0,1))),((3,1),(826,(0,0))),((4,0),(827,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_250_checked : successorFastRowCheck layer8 row7_250 row7_250choice = true := by decide
def row7_251 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]
def row7_251choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1044,(1,0))),((0,-1),(534,(0,1))),((0,1),(421,(0,0))),((0,2),(727,(0,0))),((0,3),(775,(0,0))),((1,-1),(1475,(0,1))),((1,4),(805,(0,0))),((2,0),(816,(0,0))),((2,3),(828,(0,0))),((3,1),(829,(0,0))),((3,2),(830,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_251_checked : successorFastRowCheck layer8 row7_251 row7_251choice = true := by decide
def row7_252 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)]
def row7_252choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1045,(1,0))),((0,-1),(535,(0,1))),((0,1),(422,(0,0))),((0,2),(728,(0,0))),((0,3),(776,(0,0))),((1,-1),(1476,(0,1))),((1,4),(806,(0,0))),((2,0),(817,(0,0))),((2,2),(828,(0,0))),((2,4),(831,(0,0))),((3,1),(832,(0,0))),((3,3),(833,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_252_checked : successorFastRowCheck layer8 row7_252 row7_252choice = true := by decide
def row7_253 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]
def row7_253choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1046,(1,0))),((0,-1),(536,(0,1))),((0,1),(423,(0,0))),((0,2),(729,(0,0))),((0,3),(777,(0,0))),((1,-1),(1477,(0,1))),((1,4),(808,(0,0))),((2,0),(819,(0,0))),((2,2),(829,(0,0))),((2,3),(832,(0,0))),((3,0),(834,(0,0))),((3,2),(835,(0,0))),((4,1),(836,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_253_checked : successorFastRowCheck layer8 row7_253 row7_253choice = true := by decide
def row7_254 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]
def row7_254choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1047,(1,0))),((0,-1),(537,(0,1))),((0,1),(424,(0,0))),((0,2),(730,(0,0))),((0,3),(778,(0,0))),((1,-1),(1478,(0,1))),((1,4),(809,(0,0))),((2,0),(820,(0,0))),((2,1),(828,(0,0))),((2,4),(837,(0,0))),((3,2),(838,(0,0))),((3,3),(839,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_254_checked : successorFastRowCheck layer8 row7_254 row7_254choice = true := by decide
def row7_255 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]
def row7_255choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1048,(1,0))),((0,-1),(538,(0,1))),((0,1),(425,(0,0))),((0,2),(731,(0,0))),((0,3),(779,(0,0))),((1,-1),(1479,(0,1))),((1,4),(811,(0,0))),((2,0),(822,(0,0))),((2,1),(830,(0,0))),((2,3),(838,(0,0))),((3,1),(840,(0,0))),((3,3),(841,(0,0))),((4,2),(842,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_255_checked : successorFastRowCheck layer8 row7_255 row7_255choice = true := by decide
def Closure7C031rows : List (List GridPoint) := [row7_248,row7_249,row7_250,row7_251,row7_252,row7_253,row7_254,row7_255]
theorem Closure7C031_closed : ∀ row ∈ Closure7C031rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C031rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_248choice,row7_248_checked⟩
  · subst row
    exact ⟨row7_249choice,row7_249_checked⟩
  · subst row
    exact ⟨row7_250choice,row7_250_checked⟩
  · subst row
    exact ⟨row7_251choice,row7_251_checked⟩
  · subst row
    exact ⟨row7_252choice,row7_252_checked⟩
  · subst row
    exact ⟨row7_253choice,row7_253_checked⟩
  · subst row
    exact ⟨row7_254choice,row7_254_checked⟩
  · subst row
    exact ⟨row7_255choice,row7_255_checked⟩
end Polyomino57
