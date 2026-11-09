import ASEPCheck

/-! Kernel checks of certificate chunks 40..43 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk40_ok : (certChunk40.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk41_ok : (certChunk41.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk42_ok : (certChunk42.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk43_ok : (certChunk43.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
