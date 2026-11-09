import ASEPCheck

/-! Kernel checks of certificate chunks 8..11 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk8_ok : (certChunk8.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk9_ok : (certChunk9.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk10_ok : (certChunk10.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk11_ok : (certChunk11.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
