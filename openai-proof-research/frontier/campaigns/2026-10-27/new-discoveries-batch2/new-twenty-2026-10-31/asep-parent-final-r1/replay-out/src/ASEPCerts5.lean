import ASEPCheck

/-! Kernel checks of certificate chunks 20..23 (generated). -/

namespace ASEP

set_option maxRecDepth 100000 in
theorem chunk20_ok : (certChunk20.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk21_ok : (certChunk21.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk22_ok : (certChunk22.all fun N => chk (decode N)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunk23_ok : (certChunk23.all fun N => chk (decode N)) = true := by
  decide +kernel

end ASEP
