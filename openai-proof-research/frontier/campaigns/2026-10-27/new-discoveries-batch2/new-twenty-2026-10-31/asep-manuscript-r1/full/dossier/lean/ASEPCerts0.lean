import ASEPCheck

/-! Kernel checks of certificate chunks 0..3 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk0_ok : (certChunk0.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk1_ok : (certChunk1.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk2_ok : (certChunk2.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk3_ok : (certChunk3.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
