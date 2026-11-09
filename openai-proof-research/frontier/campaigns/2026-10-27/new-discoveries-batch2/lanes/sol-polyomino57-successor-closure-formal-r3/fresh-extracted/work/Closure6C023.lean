import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_184 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row6_184choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(674,(1,0))),((0,0),(224,(0,0))),((0,1),(382,(0,0))),((0,3),(578,(0,0))),((1,-1),(709,(0,1))),((1,4),(605,(0,0))),((2,0),(609,(0,0))),((2,1),(612,(0,0))),((2,3),(615,(0,0))),((3,2),(616,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_184_checked : successorFastRowCheck layer7 row6_184 row6_184choice = true := by decide
def row6_185 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row6_185choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(675,(1,0))),((0,0),(225,(0,0))),((0,1),(383,(0,0))),((0,3),(579,(0,0))),((1,-1),(710,(0,1))),((1,4),(606,(0,0))),((2,0),(610,(0,0))),((2,1),(613,(0,0))),((2,2),(615,(0,0))),((2,4),(617,(0,0))),((3,3),(618,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_185_checked : successorFastRowCheck layer7 row6_185 row6_185choice = true := by decide
def row6_186 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)]
def row6_186choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(676,(1,0))),((0,0),(226,(0,0))),((0,1),(384,(0,0))),((0,3),(580,(0,0))),((1,-1),(715,(0,1))),((1,3),(608,(0,0))),((2,-1),(726,(0,1))),((2,2),(619,(0,0))),((3,0),(620,(0,0))),((3,1),(621,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_186_checked : successorFastRowCheck layer7 row6_186 row6_186choice = true := by decide
def row6_187 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)]
def row6_187choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(677,(1,0))),((0,0),(227,(0,0))),((0,1),(385,(0,0))),((0,3),(581,(0,0))),((1,-1),(716,(0,1))),((1,3),(609,(0,0))),((2,-1),(727,(0,1))),((2,1),(619,(0,0))),((2,3),(622,(0,0))),((3,0),(623,(0,0))),((3,2),(624,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_187_checked : successorFastRowCheck layer7 row6_187 row6_187choice = true := by decide
def row6_188 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)]
def row6_188choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(678,(1,0))),((0,0),(228,(0,0))),((0,1),(386,(0,0))),((0,3),(582,(0,0))),((1,-1),(717,(0,1))),((1,3),(611,(0,0))),((2,-1),(729,(0,1))),((2,1),(620,(0,0))),((2,2),(623,(0,0))),((3,-1),(730,(0,1))),((3,1),(625,(0,0))),((4,0),(626,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_188_checked : successorFastRowCheck layer7 row6_188 row6_188choice = true := by decide
def row6_189 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)]
def row6_189choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(679,(1,0))),((0,0),(229,(0,0))),((0,1),(387,(0,0))),((0,3),(583,(0,0))),((1,-1),(718,(0,1))),((1,3),(612,(0,0))),((2,0),(619,(0,0))),((2,3),(627,(0,0))),((3,1),(628,(0,0))),((3,2),(629,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_189_checked : successorFastRowCheck layer7 row6_189 row6_189choice = true := by decide
def row6_190 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)]
def row6_190choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(680,(1,0))),((0,0),(230,(0,0))),((0,1),(388,(0,0))),((0,3),(584,(0,0))),((1,-1),(719,(0,1))),((1,3),(614,(0,0))),((2,0),(621,(0,0))),((2,2),(628,(0,0))),((3,0),(630,(0,0))),((3,2),(631,(0,0))),((4,1),(632,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_190_checked : successorFastRowCheck layer7 row6_190 row6_190choice = true := by decide
def row6_191 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)]
def row6_191choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(681,(1,0))),((0,0),(231,(0,0))),((0,1),(389,(0,0))),((0,3),(585,(0,0))),((1,-1),(720,(0,1))),((1,3),(615,(0,0))),((2,0),(622,(0,0))),((2,1),(627,(0,0))),((2,4),(633,(0,0))),((3,2),(634,(0,0))),((3,3),(635,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_191_checked : successorFastRowCheck layer7 row6_191 row6_191choice = true := by decide
def Closure6C023rows : List (List GridPoint) := [row6_184,row6_185,row6_186,row6_187,row6_188,row6_189,row6_190,row6_191]
theorem Closure6C023_closed : ∀ row ∈ Closure6C023rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C023rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_184choice,row6_184_checked⟩
  · subst row
    exact ⟨row6_185choice,row6_185_checked⟩
  · subst row
    exact ⟨row6_186choice,row6_186_checked⟩
  · subst row
    exact ⟨row6_187choice,row6_187_checked⟩
  · subst row
    exact ⟨row6_188choice,row6_188_checked⟩
  · subst row
    exact ⟨row6_189choice,row6_189_checked⟩
  · subst row
    exact ⟨row6_190choice,row6_190_checked⟩
  · subst row
    exact ⟨row6_191choice,row6_191_checked⟩
end Polyomino57
