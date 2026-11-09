import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert0_5_0 : CutCert G color0 5 0 (cut0 5 0) (side0 5 0) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_5_1 : CutCert G color0 5 1 (cut0 5 1) (side0 5 1) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_5_2 : CutCert G color0 5 2 (cut0 5 2) (side0 5 2) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_5_3 : CutCert G color0 5 3 (cut0 5 3) (side0 5 3) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_5_4 : CutCert G color0 5 4 (cut0 5 4) (side0 5 4) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_5_6 : CutCert G color0 5 6 (cut0 5 6) (side0 5 6) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_5_7 : CutCert G color0 5 7 (cut0 5 7) (side0 5 7) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
end Rainbow
