import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert0_0_1 : CutCert G color0 0 1 (cut0 0 1) (side0 0 1) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
end Rainbow
