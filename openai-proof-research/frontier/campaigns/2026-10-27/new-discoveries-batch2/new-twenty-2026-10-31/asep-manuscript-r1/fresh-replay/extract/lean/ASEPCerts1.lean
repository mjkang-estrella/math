import ASEPCheck

/-! Kernel checks of certificate chunks 4..7 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk4_ok : (certChunk4.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk5_ok : (certChunk5.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk6_ok : (certChunk6.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk7_ok : (certChunk7.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
