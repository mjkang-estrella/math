import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert0_1_0 : CutCert G color0 1 0 (cut0 1 0) (side0 1 0) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_1_2 : CutCert G color0 1 2 (cut0 1 2) (side0 1 2) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_1_3 : CutCert G color0 1 3 (cut0 1 3) (side0 1 3) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_1_4 : CutCert G color0 1 4 (cut0 1 4) (side0 1 4) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_1_5 : CutCert G color0 1 5 (cut0 1 5) (side0 1 5) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_1_6 : CutCert G color0 1 6 (cut0 1 6) (side0 1 6) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_1_7 : CutCert G color0 1 7 (cut0 1 7) (side0 1 7) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
end Rainbow
