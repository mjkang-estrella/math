import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_376 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1)]
def row7_376choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1698,(1,0))),((-1,2),(2205,(1,0))),((-1,3),(2537,(1,0))),((0,0),(141,(0,0))),((0,4),(1176,(0,0))),((1,0),(1207,(0,0))),((1,2),(1220,(0,0))),((1,3),(1226,(0,0))),((2,-1),(1927,(0,1))),((2,2),(1230,(0,0))),((3,0),(1232,(0,0))),((3,2),(1234,(0,0))),((4,1),(1235,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_376_checked : successorFastRowCheck layer8 row7_376 row7_376choice = true := by decide
def row7_377 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1)]
def row7_377choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1699,(1,0))),((-1,2),(2206,(1,0))),((-1,3),(2538,(1,0))),((0,0),(145,(0,0))),((0,4),(1177,(0,0))),((1,0),(1213,(0,0))),((1,2),(1221,(0,0))),((1,3),(1227,(0,0))),((2,0),(1232,(0,0))),((2,2),(1236,(0,0))),((3,-1),(1929,(0,1))),((3,2),(1237,(0,0))),((4,0),(1238,(0,0))),((4,1),(1239,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_377_checked : successorFastRowCheck layer8 row7_377 row7_377choice = true := by decide
def row7_378 : List GridPoint := [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2)]
def row7_378choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1700,(1,0))),((-1,2),(2207,(1,0))),((-1,3),(2539,(1,0))),((0,0),(157,(0,0))),((0,4),(1178,(0,0))),((1,0),(1216,(0,0))),((1,1),(1218,(0,0))),((1,3),(1241,(0,0))),((2,-1),(1930,(0,1))),((2,3),(1242,(0,0))),((3,0),(1243,(0,0))),((3,1),(1244,(0,0))),((3,2),(1245,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_378_checked : successorFastRowCheck layer8 row7_378 row7_378choice = true := by decide
def row7_379 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_379choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1701,(1,0))),((-1,2),(2208,(1,0))),((0,0),(194,(0,0))),((0,3),(1179,(0,0))),((0,4),(1249,(0,0))),((1,-1),(1931,(0,1))),((1,5),(1250,(0,0))),((2,0),(1251,(0,0))),((2,1),(1252,(0,0))),((2,2),(1253,(0,0))),((2,3),(1254,(0,0))),((2,4),(1255,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_379_checked : successorFastRowCheck layer8 row7_379 row7_379choice = true := by decide
def row7_380 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row7_380choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1702,(1,0))),((-1,2),(2209,(1,0))),((0,0),(195,(0,0))),((0,3),(1180,(0,0))),((1,-1),(1933,(0,1))),((1,4),(1251,(0,0))),((2,-1),(1975,(0,1))),((2,1),(1256,(0,0))),((2,2),(1257,(0,0))),((2,3),(1258,(0,0))),((3,0),(1259,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_380_checked : successorFastRowCheck layer8 row7_380 row7_380choice = true := by decide
def row7_381 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row7_381choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1703,(1,0))),((-1,2),(2210,(1,0))),((0,0),(196,(0,0))),((0,3),(1181,(0,0))),((1,-1),(1934,(0,1))),((1,4),(1252,(0,0))),((2,0),(1256,(0,0))),((2,2),(1260,(0,0))),((2,3),(1261,(0,0))),((3,1),(1262,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_381_checked : successorFastRowCheck layer8 row7_381 row7_381choice = true := by decide
def row7_382 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row7_382choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1704,(1,0))),((-1,2),(2211,(1,0))),((0,0),(197,(0,0))),((0,3),(1182,(0,0))),((1,-1),(1935,(0,1))),((1,4),(1253,(0,0))),((2,0),(1257,(0,0))),((2,1),(1260,(0,0))),((2,3),(1263,(0,0))),((3,2),(1264,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_382_checked : successorFastRowCheck layer8 row7_382 row7_382choice = true := by decide
def row7_383 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row7_383choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1705,(1,0))),((-1,2),(2212,(1,0))),((0,0),(198,(0,0))),((0,3),(1183,(0,0))),((1,-1),(1936,(0,1))),((1,4),(1254,(0,0))),((2,0),(1258,(0,0))),((2,1),(1261,(0,0))),((2,2),(1263,(0,0))),((2,4),(1265,(0,0))),((3,3),(1266,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_383_checked : successorFastRowCheck layer8 row7_383 row7_383choice = true := by decide
def Closure7C047rows : List (List GridPoint) := [row7_376,row7_377,row7_378,row7_379,row7_380,row7_381,row7_382,row7_383]
theorem Closure7C047_closed : ∀ row ∈ Closure7C047rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C047rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_376choice,row7_376_checked⟩
  · subst row
    exact ⟨row7_377choice,row7_377_checked⟩
  · subst row
    exact ⟨row7_378choice,row7_378_checked⟩
  · subst row
    exact ⟨row7_379choice,row7_379_checked⟩
  · subst row
    exact ⟨row7_380choice,row7_380_checked⟩
  · subst row
    exact ⟨row7_381choice,row7_381_checked⟩
  · subst row
    exact ⟨row7_382choice,row7_382_checked⟩
  · subst row
    exact ⟨row7_383choice,row7_383_checked⟩
end Polyomino57
