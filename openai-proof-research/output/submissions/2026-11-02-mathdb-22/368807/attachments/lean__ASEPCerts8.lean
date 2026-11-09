import ASEPCheck

/-! Kernel checks of certificate chunks 32..35 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk32_ok : (certChunk32.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk33_ok : (certChunk33.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk34_ok : (certChunk34.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk35_ok : (certChunk35.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
