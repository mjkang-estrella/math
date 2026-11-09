import ASEPCheck

/-! Kernel checks of certificate chunks 36..39 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk36_ok : (certChunk36.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk37_ok : (certChunk37.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk38_ok : (certChunk38.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk39_ok : (certChunk39.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
