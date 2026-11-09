import ASEPCheck

/-! Kernel checks of certificate chunks 16..19 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk16_ok : (certChunk16.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk17_ok : (certChunk17.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk18_ok : (certChunk18.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk19_ok : (certChunk19.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
