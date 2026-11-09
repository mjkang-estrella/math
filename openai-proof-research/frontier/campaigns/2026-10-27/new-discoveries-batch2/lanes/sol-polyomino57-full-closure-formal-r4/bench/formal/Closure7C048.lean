import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_384 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)]
def row7_384choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1706,(1,0))),((-1,2),(2213,(1,0))),((0,0),(199,(0,0))),((0,3),(1184,(0,0))),((1,-1),(1941,(0,1))),((1,3),(1256,(0,0))),((2,-1),(1976,(0,1))),((2,2),(1267,(0,0))),((3,0),(1268,(0,0))),((3,1),(1269,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_384_checked : successorFastRowCheck layer8 row7_384 row7_384choice = true := by decide
def row7_385 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)]
def row7_385choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1707,(1,0))),((-1,2),(2214,(1,0))),((0,0),(200,(0,0))),((0,3),(1185,(0,0))),((1,-1),(1942,(0,1))),((1,3),(1257,(0,0))),((2,-1),(1977,(0,1))),((2,1),(1267,(0,0))),((2,3),(1270,(0,0))),((3,0),(1271,(0,0))),((3,2),(1272,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_385_checked : successorFastRowCheck layer8 row7_385 row7_385choice = true := by decide
def row7_386 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)]
def row7_386choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1708,(1,0))),((-1,2),(2215,(1,0))),((0,0),(201,(0,0))),((0,3),(1186,(0,0))),((1,-1),(1943,(0,1))),((1,3),(1259,(0,0))),((2,-1),(1979,(0,1))),((2,1),(1268,(0,0))),((2,2),(1271,(0,0))),((3,-1),(1980,(0,1))),((3,1),(1273,(0,0))),((4,0),(1274,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_386_checked : successorFastRowCheck layer8 row7_386 row7_386choice = true := by decide
def row7_387 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)]
def row7_387choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1709,(1,0))),((-1,2),(2216,(1,0))),((0,0),(202,(0,0))),((0,3),(1187,(0,0))),((1,-1),(1944,(0,1))),((1,3),(1260,(0,0))),((2,0),(1267,(0,0))),((2,3),(1275,(0,0))),((3,1),(1276,(0,0))),((3,2),(1277,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_387_checked : successorFastRowCheck layer8 row7_387 row7_387choice = true := by decide
def row7_388 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)]
def row7_388choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1710,(1,0))),((-1,2),(2217,(1,0))),((0,0),(203,(0,0))),((0,3),(1188,(0,0))),((1,-1),(1945,(0,1))),((1,3),(1262,(0,0))),((2,0),(1269,(0,0))),((2,2),(1276,(0,0))),((3,0),(1278,(0,0))),((3,2),(1279,(0,0))),((4,1),(1280,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_388_checked : successorFastRowCheck layer8 row7_388 row7_388choice = true := by decide
def row7_389 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)]
def row7_389choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1711,(1,0))),((-1,2),(2218,(1,0))),((0,0),(204,(0,0))),((0,3),(1189,(0,0))),((1,-1),(1946,(0,1))),((1,3),(1263,(0,0))),((2,0),(1270,(0,0))),((2,1),(1275,(0,0))),((2,4),(1281,(0,0))),((3,2),(1282,(0,0))),((3,3),(1283,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_389_checked : successorFastRowCheck layer8 row7_389 row7_389choice = true := by decide
def row7_390 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)]
def row7_390choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1712,(1,0))),((-1,2),(2219,(1,0))),((0,0),(205,(0,0))),((0,3),(1190,(0,0))),((1,-1),(1947,(0,1))),((1,3),(1264,(0,0))),((2,0),(1272,(0,0))),((2,1),(1277,(0,0))),((2,3),(1282,(0,0))),((3,1),(1284,(0,0))),((3,3),(1285,(0,0))),((4,2),(1286,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_390_checked : successorFastRowCheck layer8 row7_390 row7_390choice = true := by decide
def row7_391 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)]
def row7_391choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1713,(1,0))),((-1,2),(2220,(1,0))),((0,0),(206,(0,0))),((0,3),(1205,(0,0))),((1,-1),(1956,(0,1))),((1,2),(1267,(0,0))),((2,-1),(1981,(0,1))),((2,3),(1288,(0,0))),((3,0),(1289,(0,0))),((3,1),(1290,(0,0))),((3,2),(1291,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_391_checked : successorFastRowCheck layer8 row7_391 row7_391choice = true := by decide
def Closure7C048rows : List (List GridPoint) := [row7_384,row7_385,row7_386,row7_387,row7_388,row7_389,row7_390,row7_391]
theorem Closure7C048_closed : ∀ row ∈ Closure7C048rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C048rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_384choice,row7_384_checked⟩
  · subst row
    exact ⟨row7_385choice,row7_385_checked⟩
  · subst row
    exact ⟨row7_386choice,row7_386_checked⟩
  · subst row
    exact ⟨row7_387choice,row7_387_checked⟩
  · subst row
    exact ⟨row7_388choice,row7_388_checked⟩
  · subst row
    exact ⟨row7_389choice,row7_389_checked⟩
  · subst row
    exact ⟨row7_390choice,row7_390_checked⟩
  · subst row
    exact ⟨row7_391choice,row7_391_checked⟩
end Polyomino57
