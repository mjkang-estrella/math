import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_296 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)]
def row7_296choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1089,(1,0))),((0,-1),(597,(0,1))),((0,1),(466,(0,0))),((1,-1),(1561,(0,1))),((1,2),(877,(0,0))),((2,0),(922,(0,0))),((2,3),(959,(0,0))),((3,-1),(1743,(0,1))),((3,2),(967,(0,0))),((4,0),(968,(0,0))),((4,1),(969,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_296_checked : successorFastRowCheck layer8 row7_296 row7_296choice = true := by decide
def row7_297 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)]
def row7_297choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1090,(1,0))),((0,-1),(598,(0,1))),((0,1),(467,(0,0))),((1,-1),(1562,(0,1))),((1,2),(878,(0,0))),((2,0),(925,(0,0))),((2,3),(960,(0,0))),((3,0),(967,(0,0))),((3,3),(970,(0,0))),((4,1),(971,(0,0))),((4,2),(972,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_297_checked : successorFastRowCheck layer8 row7_297 row7_297choice = true := by decide
def row7_298 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]
def row7_298choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1091,(1,0))),((0,-1),(599,(0,1))),((0,1),(468,(0,0))),((1,-1),(1563,(0,1))),((1,2),(879,(0,0))),((2,0),(926,(0,0))),((2,3),(962,(0,0))),((3,0),(969,(0,0))),((3,2),(971,(0,0))),((4,0),(973,(0,0))),((4,2),(974,(0,0))),((5,1),(975,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_298_checked : successorFastRowCheck layer8 row7_298 row7_298choice = true := by decide
def row7_299 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)]
def row7_299choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1092,(1,0))),((0,-1),(600,(0,1))),((0,1),(469,(0,0))),((1,-1),(1564,(0,1))),((1,2),(880,(0,0))),((2,0),(927,(0,0))),((2,3),(963,(0,0))),((3,1),(970,(0,0))),((3,4),(976,(0,0))),((4,2),(977,(0,0))),((4,3),(978,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_299_checked : successorFastRowCheck layer8 row7_299 row7_299choice = true := by decide
def row7_300 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]
def row7_300choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1093,(1,0))),((0,-1),(601,(0,1))),((0,1),(470,(0,0))),((1,-1),(1565,(0,1))),((1,2),(881,(0,0))),((2,0),(928,(0,0))),((2,3),(964,(0,0))),((3,1),(972,(0,0))),((3,3),(977,(0,0))),((4,1),(979,(0,0))),((4,3),(980,(0,0))),((5,2),(981,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_300_checked : successorFastRowCheck layer8 row7_300 row7_300choice = true := by decide
def row7_301 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)]
def row7_301choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1094,(1,0))),((0,-1),(603,(0,1))),((0,1),(471,(0,0))),((1,-1),(1567,(0,1))),((1,2),(882,(0,0))),((2,0),(929,(0,0))),((2,2),(967,(0,0))),((3,-1),(1744,(0,1))),((3,3),(983,(0,0))),((4,0),(984,(0,0))),((4,1),(985,(0,0))),((4,2),(986,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_301_checked : successorFastRowCheck layer8 row7_301 row7_301choice = true := by decide
def row7_302 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)]
def row7_302choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1095,(1,0))),((0,-1),(604,(0,1))),((0,1),(472,(0,0))),((1,-1),(1568,(0,1))),((1,2),(883,(0,0))),((2,0),(930,(0,0))),((2,2),(968,(0,0))),((3,-1),(1746,(0,1))),((3,2),(984,(0,0))),((4,-1),(1748,(0,1))),((4,1),(987,(0,0))),((5,0),(988,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_302_checked : successorFastRowCheck layer8 row7_302 row7_302choice = true := by decide
def row7_303 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]
def row7_303choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1096,(1,0))),((0,-1),(605,(0,1))),((0,1),(473,(0,0))),((1,-1),(1569,(0,1))),((1,2),(884,(0,0))),((2,0),(931,(0,0))),((2,2),(969,(0,0))),((3,-1),(1747,(0,1))),((3,2),(985,(0,0))),((4,0),(987,(0,0))),((4,2),(989,(0,0))),((5,1),(990,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_303_checked : successorFastRowCheck layer8 row7_303 row7_303choice = true := by decide
def Closure7C037rows : List (List GridPoint) := [row7_296,row7_297,row7_298,row7_299,row7_300,row7_301,row7_302,row7_303]
theorem Closure7C037_closed : ∀ row ∈ Closure7C037rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C037rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_296choice,row7_296_checked⟩
  · subst row
    exact ⟨row7_297choice,row7_297_checked⟩
  · subst row
    exact ⟨row7_298choice,row7_298_checked⟩
  · subst row
    exact ⟨row7_299choice,row7_299_checked⟩
  · subst row
    exact ⟨row7_300choice,row7_300_checked⟩
  · subst row
    exact ⟨row7_301choice,row7_301_checked⟩
  · subst row
    exact ⟨row7_302choice,row7_302_checked⟩
  · subst row
    exact ⟨row7_303choice,row7_303_checked⟩
end Polyomino57
