import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert0_3_0 : CutCert G color0 3 0 (cut0 3 0) (side0 3 0) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_3_1 : CutCert G color0 3 1 (cut0 3 1) (side0 3 1) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_3_2 : CutCert G color0 3 2 (cut0 3 2) (side0 3 2) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_3_4 : CutCert G color0 3 4 (cut0 3 4) (side0 3 4) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_3_5 : CutCert G color0 3 5 (cut0 3 5) (side0 3 5) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_3_6 : CutCert G color0 3 6 (cut0 3 6) (side0 3 6) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_3_7 : CutCert G color0 3 7 (cut0 3 7) (side0 3 7) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
end Rainbow
