import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert0_0_1 : CutCert G color0 0 1 (cut0 0 1) (side0 0 1) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_0_2 : CutCert G color0 0 2 (cut0 0 2) (side0 0 2) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_0_3 : CutCert G color0 0 3 (cut0 0 3) (side0 0 3) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_0_4 : CutCert G color0 0 4 (cut0 0 4) (side0 0 4) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_0_5 : CutCert G color0 0 5 (cut0 0 5) (side0 0 5) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_0_6 : CutCert G color0 0 6 (cut0 0 6) (side0 0 6) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_0_7 : CutCert G color0 0 7 (cut0 0 7) (side0 0 7) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
end Rainbow
