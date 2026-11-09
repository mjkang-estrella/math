import ASEPCheck

/-! Kernel checks of certificate chunks 44..47 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk44_ok : (certChunk44.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk45_ok : (certChunk45.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk46_ok : (certChunk46.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk47_ok : (certChunk47.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
