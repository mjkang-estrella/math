import ASEPCheck

/-! Kernel checks of certificate chunks 12..15 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk12_ok : (certChunk12.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk13_ok : (certChunk13.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk14_ok : (certChunk14.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk15_ok : (certChunk15.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
