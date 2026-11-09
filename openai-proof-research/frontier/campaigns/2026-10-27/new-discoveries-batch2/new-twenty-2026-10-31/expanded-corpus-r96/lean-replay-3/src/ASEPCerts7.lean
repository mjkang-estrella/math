import ASEPCheck

/-! Kernel checks of certificate chunks 28..31 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk28_ok : (certChunk28.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk29_ok : (certChunk29.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk30_ok : (certChunk30.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk31_ok : (certChunk31.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
