import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_368 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)]
def row7_368choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1690,(1,0))),((-1,2),(2197,(1,0))),((-1,3),(2529,(1,0))),((0,0),(90,(0,0))),((0,4),(1167,(0,0))),((1,-1),(1911,(0,1))),((1,2),(1184,(0,0))),((1,3),(1196,(0,0))),((2,-1),(1918,(0,1))),((2,2),(1205,(0,0))),((3,0),(1206,(0,0))),((3,1),(1207,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_368_checked : successorFastRowCheck layer8 row7_368 row7_368choice = true := by decide
def row7_369 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0)]
def row7_369choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1691,(1,0))),((-1,2),(2198,(1,0))),((-1,3),(2530,(1,0))),((0,0),(91,(0,0))),((0,4),(1168,(0,0))),((1,-1),(1912,(0,1))),((1,2),(1186,(0,0))),((1,3),(1198,(0,0))),((2,-1),(1920,(0,1))),((2,1),(1206,(0,0))),((3,-1),(1921,(0,1))),((3,1),(1208,(0,0))),((4,0),(1209,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_369_checked : successorFastRowCheck layer8 row7_369 row7_369choice = true := by decide
def row7_370 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2)]
def row7_370choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1692,(1,0))),((-1,2),(2199,(1,0))),((-1,3),(2531,(1,0))),((0,0),(92,(0,0))),((0,4),(1169,(0,0))),((1,-1),(1913,(0,1))),((1,2),(1187,(0,0))),((1,3),(1199,(0,0))),((2,0),(1205,(0,0))),((2,3),(1210,(0,0))),((3,1),(1211,(0,0))),((3,2),(1212,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_370_checked : successorFastRowCheck layer8 row7_370 row7_370choice = true := by decide
def row7_371 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1)]
def row7_371choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1693,(1,0))),((-1,2),(2200,(1,0))),((-1,3),(2532,(1,0))),((0,0),(93,(0,0))),((0,4),(1170,(0,0))),((1,-1),(1914,(0,1))),((1,2),(1188,(0,0))),((1,3),(1201,(0,0))),((2,0),(1207,(0,0))),((2,2),(1211,(0,0))),((3,0),(1213,(0,0))),((3,2),(1214,(0,0))),((4,1),(1215,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_371_checked : successorFastRowCheck layer8 row7_371 row7_371choice = true := by decide
def row7_372 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)]
def row7_372choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1694,(1,0))),((-1,2),(2201,(1,0))),((-1,3),(2533,(1,0))),((0,0),(123,(0,0))),((0,4),(1171,(0,0))),((1,0),(1184,(0,0))),((1,3),(1217,(0,0))),((2,-1),(1922,(0,1))),((2,2),(1218,(0,0))),((3,0),(1219,(0,0))),((3,1),(1220,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_372_checked : successorFastRowCheck layer8 row7_372 row7_372choice = true := by decide
def row7_373 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1)]
def row7_373choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1695,(1,0))),((-1,2),(2202,(1,0))),((-1,3),(2534,(1,0))),((0,0),(132,(0,0))),((0,4),(1172,(0,0))),((1,0),(1196,(0,0))),((1,2),(1217,(0,0))),((1,4),(1222,(0,0))),((2,-1),(1923,(0,1))),((2,2),(1223,(0,0))),((2,3),(1224,(0,0))),((3,0),(1225,(0,0))),((3,1),(1226,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_373_checked : successorFastRowCheck layer8 row7_373 row7_373choice = true := by decide
def row7_374 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2)]
def row7_374choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1696,(1,0))),((-1,2),(2203,(1,0))),((-1,3),(2535,(1,0))),((0,0),(139,(0,0))),((0,4),(1174,(0,0))),((1,0),(1205,(0,0))),((1,2),(1218,(0,0))),((1,3),(1223,(0,0))),((2,-1),(1924,(0,1))),((2,3),(1228,(0,0))),((3,0),(1229,(0,0))),((3,1),(1230,(0,0))),((3,2),(1231,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_374_checked : successorFastRowCheck layer8 row7_374 row7_374choice = true := by decide
def row7_375 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0)]
def row7_375choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1697,(1,0))),((-1,2),(2204,(1,0))),((-1,3),(2536,(1,0))),((0,0),(140,(0,0))),((0,4),(1175,(0,0))),((1,0),(1206,(0,0))),((1,2),(1219,(0,0))),((1,3),(1225,(0,0))),((2,-1),(1926,(0,1))),((2,2),(1229,(0,0))),((3,-1),(1928,(0,1))),((3,1),(1232,(0,0))),((4,0),(1233,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_375_checked : successorFastRowCheck layer8 row7_375 row7_375choice = true := by decide
def Closure7C046rows : List (List GridPoint) := [row7_368,row7_369,row7_370,row7_371,row7_372,row7_373,row7_374,row7_375]
theorem Closure7C046_closed : ∀ row ∈ Closure7C046rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C046rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_368choice,row7_368_checked⟩
  · subst row
    exact ⟨row7_369choice,row7_369_checked⟩
  · subst row
    exact ⟨row7_370choice,row7_370_checked⟩
  · subst row
    exact ⟨row7_371choice,row7_371_checked⟩
  · subst row
    exact ⟨row7_372choice,row7_372_checked⟩
  · subst row
    exact ⟨row7_373choice,row7_373_checked⟩
  · subst row
    exact ⟨row7_374choice,row7_374_checked⟩
  · subst row
    exact ⟨row7_375choice,row7_375_checked⟩
end Polyomino57
