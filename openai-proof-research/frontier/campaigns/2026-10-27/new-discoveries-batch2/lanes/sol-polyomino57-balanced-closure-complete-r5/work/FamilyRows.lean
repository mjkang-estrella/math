import F7All
import SevenCoverage
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def familyRows : RowFamilyTree → List (List GridPoint)
  | .leaf rows => rows.toList
  | .branch left right => familyRows left ++ familyRows right
 theorem familyRows_mem (T : RowFamilyTree) (row : List GridPoint) :
    row ∈ familyRows T ↔ FamilyMember row T := by
  induction T with
  | leaf rows => rfl
  | branch left right ihl ihr =>
    simpa only [familyRows, FamilyMember, List.mem_append] using or_congr ihl ihr
 theorem family7_rows : familyRows family7 = layer7.toList := by decide
 theorem family7_of_layer7 (row : List GridPoint) (h : row ∈ layer7.toList) :
    FamilyMember row family7 := (familyRows_mem family7 row).mp (family7_rows.symm ▸ h)
end Polyomino57
