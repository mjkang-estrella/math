import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_352 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)]
def row7_352choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1145,(1,0))),((0,-1),(696,(0,1))),((0,1),(522,(0,0))),((1,-1),(1674,(0,1))),((1,1),(953,(0,0))),((2,-1),(1826,(0,1))),((2,1),(1084,(0,0))),((3,-1),(1870,(0,1))),((3,1),(1125,(0,0))),((4,-1),(1883,(0,1))),((4,1),(1138,(0,0))),((5,-1),(1887,(0,1))),((5,1),(1142,(0,0))),((6,-1),(1888,(0,1))),((6,1),(1144,(0,0))),((7,0),(1145,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_352_checked : successorFastRowCheck layer8 row7_352 row7_352choice = true := by decide
def row7_353 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1)]
def row7_353choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1675,(1,0))),((-1,2),(2182,(1,0))),((-1,3),(2514,(1,0))),((-1,4),(2673,(1,0))),((-1,5),(2719,(1,0))),((0,0),(8,(0,0))),((0,6),(1146,(0,0))),((1,-1),(1889,(0,1))),((1,2),(1147,(0,0))),((1,3),(1148,(0,0))),((1,4),(1149,(0,0))),((1,5),(1150,(0,0))),((2,0),(1151,(0,0))),((2,1),(1152,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_353_checked : successorFastRowCheck layer8 row7_353 row7_353choice = true := by decide
def row7_354 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)]
def row7_354choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1676,(1,0))),((-1,2),(2183,(1,0))),((-1,3),(2515,(1,0))),((-1,4),(2674,(1,0))),((0,0),(30,(0,0))),((0,5),(1147,(0,0))),((1,-1),(1890,(0,1))),((1,3),(1154,(0,0))),((1,4),(1155,(0,0))),((2,0),(1156,(0,0))),((2,1),(1157,(0,0))),((2,2),(1158,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_354_checked : successorFastRowCheck layer8 row7_354 row7_354choice = true := by decide
def row7_355 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)]
def row7_355choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1677,(1,0))),((-1,2),(2184,(1,0))),((-1,3),(2516,(1,0))),((-1,4),(2675,(1,0))),((0,0),(31,(0,0))),((0,5),(1148,(0,0))),((1,-1),(1891,(0,1))),((1,2),(1154,(0,0))),((1,4),(1159,(0,0))),((2,0),(1160,(0,0))),((2,1),(1161,(0,0))),((2,3),(1162,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_355_checked : successorFastRowCheck layer8 row7_355 row7_355choice = true := by decide
def row7_356 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4)]
def row7_356choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1678,(1,0))),((-1,2),(2185,(1,0))),((-1,3),(2517,(1,0))),((-1,4),(2676,(1,0))),((0,0),(32,(0,0))),((0,5),(1149,(0,0))),((1,-1),(1892,(0,1))),((1,2),(1155,(0,0))),((1,3),(1159,(0,0))),((1,5),(1163,(0,0))),((2,0),(1164,(0,0))),((2,1),(1165,(0,0))),((2,4),(1166,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_356_checked : successorFastRowCheck layer8 row7_356 row7_356choice = true := by decide
def row7_357 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0)]
def row7_357choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1679,(1,0))),((-1,2),(2186,(1,0))),((-1,3),(2518,(1,0))),((-1,4),(2677,(1,0))),((0,0),(33,(0,0))),((0,5),(1151,(0,0))),((1,-1),(1894,(0,1))),((1,2),(1156,(0,0))),((1,3),(1160,(0,0))),((1,4),(1164,(0,0))),((2,-1),(1896,(0,1))),((2,1),(1167,(0,0))),((3,0),(1168,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_357_checked : successorFastRowCheck layer8 row7_357 row7_357choice = true := by decide
def row7_358 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1)]
def row7_358choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1680,(1,0))),((-1,2),(2187,(1,0))),((-1,3),(2519,(1,0))),((-1,4),(2678,(1,0))),((0,0),(34,(0,0))),((0,5),(1152,(0,0))),((1,-1),(1895,(0,1))),((1,2),(1157,(0,0))),((1,3),(1161,(0,0))),((1,4),(1165,(0,0))),((2,0),(1167,(0,0))),((2,2),(1169,(0,0))),((3,1),(1170,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_358_checked : successorFastRowCheck layer8 row7_358 row7_358choice = true := by decide
def row7_359 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1)]
def row7_359choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1681,(1,0))),((-1,2),(2188,(1,0))),((-1,3),(2520,(1,0))),((-1,4),(2679,(1,0))),((0,0),(57,(0,0))),((0,5),(1153,(0,0))),((1,0),(1167,(0,0))),((1,2),(1171,(0,0))),((1,3),(1172,(0,0))),((1,4),(1173,(0,0))),((2,-1),(1897,(0,1))),((2,2),(1174,(0,0))),((3,0),(1175,(0,0))),((3,1),(1176,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_359_checked : successorFastRowCheck layer8 row7_359 row7_359choice = true := by decide
def Closure7C044rows : List (List GridPoint) := [row7_352,row7_353,row7_354,row7_355,row7_356,row7_357,row7_358,row7_359]
theorem Closure7C044_closed : ∀ row ∈ Closure7C044rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C044rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_352choice,row7_352_checked⟩
  · subst row
    exact ⟨row7_353choice,row7_353_checked⟩
  · subst row
    exact ⟨row7_354choice,row7_354_checked⟩
  · subst row
    exact ⟨row7_355choice,row7_355_checked⟩
  · subst row
    exact ⟨row7_356choice,row7_356_checked⟩
  · subst row
    exact ⟨row7_357choice,row7_357_checked⟩
  · subst row
    exact ⟨row7_358choice,row7_358_checked⟩
  · subst row
    exact ⟨row7_359choice,row7_359_checked⟩
end Polyomino57
