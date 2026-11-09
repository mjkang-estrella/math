import ASEPCheck

/-! Kernel checks of certificate chunks 24..27 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk24_ok : (certChunk24.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk25_ok : (certChunk25.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk26_ok : (certChunk26.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk27_ok : (certChunk27.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
