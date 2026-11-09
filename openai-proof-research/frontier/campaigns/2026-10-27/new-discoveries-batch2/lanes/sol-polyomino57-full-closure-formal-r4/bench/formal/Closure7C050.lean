import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_400 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2)]
def row7_400choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1722,(1,0))),((-1,2),(2229,(1,0))),((0,0),(215,(0,0))),((0,3),(1214,(0,0))),((1,-1),(1966,(0,1))),((1,2),(1279,(0,0))),((2,0),(1294,(0,0))),((2,2),(1306,(0,0))),((3,0),(1310,(0,0))),((3,3),(1313,(0,0))),((4,1),(1314,(0,0))),((4,2),(1315,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_400_checked : successorFastRowCheck layer8 row7_400 row7_400choice = true := by decide
def row7_401 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1)]
def row7_401choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1723,(1,0))),((-1,2),(2230,(1,0))),((0,0),(216,(0,0))),((0,3),(1215,(0,0))),((1,-1),(1967,(0,1))),((1,2),(1280,(0,0))),((2,0),(1295,(0,0))),((2,2),(1307,(0,0))),((3,0),(1312,(0,0))),((3,2),(1314,(0,0))),((4,0),(1316,(0,0))),((4,2),(1317,(0,0))),((5,1),(1318,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_401_checked : successorFastRowCheck layer8 row7_401 row7_401choice = true := by decide
def row7_402 : List GridPoint := [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)]
def row7_402choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1724,(1,0))),((-1,2),(2231,(1,0))),((0,0),(231,(0,0))),((0,3),(1216,(0,0))),((1,-1),(1968,(0,1))),((1,1),(1267,(0,0))),((1,3),(1319,(0,0))),((2,-1),(1995,(0,1))),((2,3),(1320,(0,0))),((3,0),(1321,(0,0))),((3,1),(1322,(0,0))),((3,2),(1323,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_402_checked : successorFastRowCheck layer8 row7_402 row7_402choice = true := by decide
def row7_403 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_403choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1725,(1,0))),((-1,2),(2232,(1,0))),((0,0),(266,(0,0))),((0,3),(1217,(0,0))),((1,0),(1256,(0,0))),((1,4),(1324,(0,0))),((2,-1),(1996,(0,1))),((2,2),(1325,(0,0))),((2,3),(1326,(0,0))),((3,0),(1327,(0,0))),((3,1),(1328,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_403_checked : successorFastRowCheck layer8 row7_403 row7_403choice = true := by decide
def row7_404 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)]
def row7_404choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1726,(1,0))),((-1,2),(2233,(1,0))),((0,0),(274,(0,0))),((0,3),(1218,(0,0))),((1,0),(1267,(0,0))),((1,3),(1325,(0,0))),((2,-1),(1997,(0,1))),((2,3),(1330,(0,0))),((3,0),(1331,(0,0))),((3,1),(1332,(0,0))),((3,2),(1333,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_404_checked : successorFastRowCheck layer8 row7_404 row7_404choice = true := by decide
def row7_405 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)]
def row7_405choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1727,(1,0))),((-1,2),(2234,(1,0))),((0,0),(275,(0,0))),((0,3),(1219,(0,0))),((1,0),(1268,(0,0))),((1,3),(1327,(0,0))),((2,-1),(1999,(0,1))),((2,2),(1331,(0,0))),((3,-1),(2001,(0,1))),((3,1),(1334,(0,0))),((4,0),(1335,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_405_checked : successorFastRowCheck layer8 row7_405 row7_405choice = true := by decide
def row7_406 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)]
def row7_406choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1728,(1,0))),((-1,2),(2235,(1,0))),((0,0),(276,(0,0))),((0,3),(1220,(0,0))),((1,0),(1269,(0,0))),((1,3),(1328,(0,0))),((2,-1),(2000,(0,1))),((2,2),(1332,(0,0))),((3,0),(1334,(0,0))),((3,2),(1336,(0,0))),((4,1),(1337,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_406_checked : successorFastRowCheck layer8 row7_406 row7_406choice = true := by decide
def row7_407 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)]
def row7_407choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1729,(1,0))),((-1,2),(2236,(1,0))),((0,0),(280,(0,0))),((0,3),(1221,(0,0))),((1,0),(1278,(0,0))),((1,3),(1329,(0,0))),((2,0),(1334,(0,0))),((2,2),(1338,(0,0))),((3,-1),(2002,(0,1))),((3,2),(1339,(0,0))),((4,0),(1340,(0,0))),((4,1),(1341,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_407_checked : successorFastRowCheck layer8 row7_407 row7_407choice = true := by decide
def Closure7C050rows : List (List GridPoint) := [row7_400,row7_401,row7_402,row7_403,row7_404,row7_405,row7_406,row7_407]
theorem Closure7C050_closed : ∀ row ∈ Closure7C050rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C050rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_400choice,row7_400_checked⟩
  · subst row
    exact ⟨row7_401choice,row7_401_checked⟩
  · subst row
    exact ⟨row7_402choice,row7_402_checked⟩
  · subst row
    exact ⟨row7_403choice,row7_403_checked⟩
  · subst row
    exact ⟨row7_404choice,row7_404_checked⟩
  · subst row
    exact ⟨row7_405choice,row7_405_checked⟩
  · subst row
    exact ⟨row7_406choice,row7_406_checked⟩
  · subst row
    exact ⟨row7_407choice,row7_407_checked⟩
end Polyomino57
