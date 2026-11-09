import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_344 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)]
def row7_344choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1137,(1,0))),((0,-1),(684,(0,1))),((0,1),(514,(0,0))),((1,-1),(1662,(0,1))),((1,1),(945,(0,0))),((2,-1),(1814,(0,1))),((2,1),(1076,(0,0))),((3,-1),(1856,(0,1))),((3,2),(1114,(0,0))),((4,-1),(1872,(0,1))),((4,2),(1121,(0,0))),((5,0),(1122,(0,0))),((5,1),(1123,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_344_checked : successorFastRowCheck layer8 row7_344 row7_344choice = true := by decide
def row7_345 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)]
def row7_345choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1138,(1,0))),((0,-1),(685,(0,1))),((0,1),(515,(0,0))),((1,-1),(1663,(0,1))),((1,1),(946,(0,0))),((2,-1),(1815,(0,1))),((2,1),(1077,(0,0))),((3,-1),(1857,(0,1))),((3,2),(1116,(0,0))),((4,-1),(1874,(0,1))),((4,1),(1122,(0,0))),((5,-1),(1875,(0,1))),((5,1),(1124,(0,0))),((6,0),(1125,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_345_checked : successorFastRowCheck layer8 row7_345 row7_345choice = true := by decide
def row7_346 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)]
def row7_346choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1139,(1,0))),((0,-1),(686,(0,1))),((0,1),(516,(0,0))),((1,-1),(1664,(0,1))),((1,1),(947,(0,0))),((2,-1),(1816,(0,1))),((2,1),(1078,(0,0))),((3,-1),(1858,(0,1))),((3,2),(1117,(0,0))),((4,0),(1121,(0,0))),((4,3),(1126,(0,0))),((5,1),(1127,(0,0))),((5,2),(1128,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_346_checked : successorFastRowCheck layer8 row7_346 row7_346choice = true := by decide
def row7_347 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)]
def row7_347choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1140,(1,0))),((0,-1),(687,(0,1))),((0,1),(517,(0,0))),((1,-1),(1665,(0,1))),((1,1),(948,(0,0))),((2,-1),(1817,(0,1))),((2,1),(1079,(0,0))),((3,-1),(1859,(0,1))),((3,2),(1118,(0,0))),((4,0),(1123,(0,0))),((4,2),(1127,(0,0))),((5,0),(1129,(0,0))),((5,2),(1130,(0,0))),((6,1),(1131,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_347_checked : successorFastRowCheck layer8 row7_347 row7_347choice = true := by decide
def row7_348 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)]
def row7_348choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1141,(1,0))),((0,-1),(691,(0,1))),((0,1),(518,(0,0))),((1,-1),(1669,(0,1))),((1,1),(949,(0,0))),((2,-1),(1821,(0,1))),((2,1),(1080,(0,0))),((3,-1),(1865,(0,1))),((3,1),(1121,(0,0))),((3,2),(1132,(0,0))),((4,-1),(1876,(0,1))),((4,3),(1133,(0,0))),((5,0),(1134,(0,0))),((5,1),(1135,(0,0))),((5,2),(1136,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_348_checked : successorFastRowCheck layer8 row7_348 row7_348choice = true := by decide
def row7_349 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)]
def row7_349choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1142,(1,0))),((0,-1),(692,(0,1))),((0,1),(519,(0,0))),((1,-1),(1670,(0,1))),((1,1),(950,(0,0))),((2,-1),(1822,(0,1))),((2,1),(1081,(0,0))),((3,-1),(1866,(0,1))),((3,1),(1122,(0,0))),((4,-1),(1878,(0,1))),((4,2),(1134,(0,0))),((5,-1),(1884,(0,1))),((5,1),(1137,(0,0))),((6,0),(1138,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_349_checked : successorFastRowCheck layer8 row7_349 row7_349choice = true := by decide
def row7_350 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)]
def row7_350choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1143,(1,0))),((0,-1),(693,(0,1))),((0,1),(520,(0,0))),((1,-1),(1671,(0,1))),((1,1),(951,(0,0))),((2,-1),(1823,(0,1))),((2,1),(1082,(0,0))),((3,-1),(1867,(0,1))),((3,1),(1123,(0,0))),((4,-1),(1879,(0,1))),((4,2),(1135,(0,0))),((5,0),(1137,(0,0))),((5,2),(1139,(0,0))),((6,1),(1140,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_350_checked : successorFastRowCheck layer8 row7_350 row7_350choice = true := by decide
def row7_351 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)]
def row7_351choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1144,(1,0))),((0,-1),(695,(0,1))),((0,1),(521,(0,0))),((1,-1),(1673,(0,1))),((1,1),(952,(0,0))),((2,-1),(1825,(0,1))),((2,1),(1083,(0,0))),((3,-1),(1869,(0,1))),((3,1),(1124,(0,0))),((4,-1),(1882,(0,1))),((4,1),(1137,(0,0))),((5,-1),(1885,(0,1))),((5,2),(1141,(0,0))),((6,0),(1142,(0,0))),((6,1),(1143,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_351_checked : successorFastRowCheck layer8 row7_351 row7_351choice = true := by decide
def Closure7C043rows : List (List GridPoint) := [row7_344,row7_345,row7_346,row7_347,row7_348,row7_349,row7_350,row7_351]
theorem Closure7C043_closed : ∀ row ∈ Closure7C043rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C043rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_344choice,row7_344_checked⟩
  · subst row
    exact ⟨row7_345choice,row7_345_checked⟩
  · subst row
    exact ⟨row7_346choice,row7_346_checked⟩
  · subst row
    exact ⟨row7_347choice,row7_347_checked⟩
  · subst row
    exact ⟨row7_348choice,row7_348_checked⟩
  · subst row
    exact ⟨row7_349choice,row7_349_checked⟩
  · subst row
    exact ⟨row7_350choice,row7_350_checked⟩
  · subst row
    exact ⟨row7_351choice,row7_351_checked⟩
end Polyomino57
