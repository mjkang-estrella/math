import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_224 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row7_224choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1017,(1,0))),((-1,2),(2172,(1,0))),((0,-1),(392,(0,1))),((0,1),(197,(0,0))),((0,3),(706,(0,0))),((1,-1),(1429,(0,1))),((1,4),(720,(0,0))),((2,0),(724,(0,0))),((2,1),(727,(0,0))),((2,3),(730,(0,0))),((3,2),(731,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_224_checked : successorFastRowCheck layer8 row7_224 row7_224choice = true := by decide
def row7_225 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row7_225choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1018,(1,0))),((-1,2),(2173,(1,0))),((0,-1),(393,(0,1))),((0,1),(198,(0,0))),((0,3),(707,(0,0))),((1,-1),(1430,(0,1))),((1,4),(721,(0,0))),((2,0),(725,(0,0))),((2,1),(728,(0,0))),((2,2),(730,(0,0))),((2,4),(732,(0,0))),((3,3),(733,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_225_checked : successorFastRowCheck layer8 row7_225 row7_225choice = true := by decide
def row7_226 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)]
def row7_226choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1019,(1,0))),((-1,2),(2174,(1,0))),((0,-1),(395,(0,1))),((0,1),(199,(0,0))),((0,3),(708,(0,0))),((1,-1),(1435,(0,1))),((1,3),(723,(0,0))),((2,-1),(1444,(0,1))),((2,2),(734,(0,0))),((3,0),(735,(0,0))),((3,1),(736,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_226_checked : successorFastRowCheck layer8 row7_226 row7_226choice = true := by decide
def row7_227 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)]
def row7_227choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1020,(1,0))),((-1,2),(2175,(1,0))),((0,-1),(396,(0,1))),((0,1),(200,(0,0))),((0,3),(709,(0,0))),((1,-1),(1436,(0,1))),((1,3),(724,(0,0))),((2,-1),(1445,(0,1))),((2,1),(734,(0,0))),((2,3),(737,(0,0))),((3,0),(738,(0,0))),((3,2),(739,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_227_checked : successorFastRowCheck layer8 row7_227 row7_227choice = true := by decide
def row7_228 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)]
def row7_228choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1021,(1,0))),((-1,2),(2176,(1,0))),((0,-1),(397,(0,1))),((0,1),(201,(0,0))),((0,3),(710,(0,0))),((1,-1),(1437,(0,1))),((1,3),(726,(0,0))),((2,-1),(1447,(0,1))),((2,1),(735,(0,0))),((2,2),(738,(0,0))),((3,-1),(1448,(0,1))),((3,1),(740,(0,0))),((4,0),(741,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_228_checked : successorFastRowCheck layer8 row7_228 row7_228choice = true := by decide
def row7_229 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)]
def row7_229choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1022,(1,0))),((-1,2),(2177,(1,0))),((0,-1),(398,(0,1))),((0,1),(202,(0,0))),((0,3),(711,(0,0))),((1,-1),(1438,(0,1))),((1,3),(727,(0,0))),((2,0),(734,(0,0))),((2,3),(742,(0,0))),((3,1),(743,(0,0))),((3,2),(744,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_229_checked : successorFastRowCheck layer8 row7_229 row7_229choice = true := by decide
def row7_230 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)]
def row7_230choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1023,(1,0))),((-1,2),(2178,(1,0))),((0,-1),(399,(0,1))),((0,1),(203,(0,0))),((0,3),(712,(0,0))),((1,-1),(1439,(0,1))),((1,3),(729,(0,0))),((2,0),(736,(0,0))),((2,2),(743,(0,0))),((3,0),(745,(0,0))),((3,2),(746,(0,0))),((4,1),(747,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_230_checked : successorFastRowCheck layer8 row7_230 row7_230choice = true := by decide
def row7_231 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)]
def row7_231choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1024,(1,0))),((-1,2),(2179,(1,0))),((0,-1),(400,(0,1))),((0,1),(204,(0,0))),((0,3),(713,(0,0))),((1,-1),(1440,(0,1))),((1,3),(730,(0,0))),((2,0),(737,(0,0))),((2,1),(742,(0,0))),((2,4),(748,(0,0))),((3,2),(749,(0,0))),((3,3),(750,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_231_checked : successorFastRowCheck layer8 row7_231 row7_231choice = true := by decide
def Closure7C028rows : List (List GridPoint) := [row7_224,row7_225,row7_226,row7_227,row7_228,row7_229,row7_230,row7_231]
theorem Closure7C028_closed : ∀ row ∈ Closure7C028rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C028rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_224choice,row7_224_checked⟩
  · subst row
    exact ⟨row7_225choice,row7_225_checked⟩
  · subst row
    exact ⟨row7_226choice,row7_226_checked⟩
  · subst row
    exact ⟨row7_227choice,row7_227_checked⟩
  · subst row
    exact ⟨row7_228choice,row7_228_checked⟩
  · subst row
    exact ⟨row7_229choice,row7_229_checked⟩
  · subst row
    exact ⟨row7_230choice,row7_230_checked⟩
  · subst row
    exact ⟨row7_231choice,row7_231_checked⟩
end Polyomino57
