import ASEPCheck

/-! Kernel check that the certificates are indexed by all cyclic orders `0 :: tl`. -/

namespace ASEP

set_option maxRecDepth 1000000 in
theorem certs_cover : certData.map (fun N => (decode N).tl) = List.permutations' l7 := by
  decide +kernel

end ASEP
