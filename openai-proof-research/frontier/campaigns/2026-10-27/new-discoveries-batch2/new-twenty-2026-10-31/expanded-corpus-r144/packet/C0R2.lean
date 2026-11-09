import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert0_2_0 : CutCert G color0 2 0 (cut0 2 0) (side0 2 0) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_2_1 : CutCert G color0 2 1 (cut0 2 1) (side0 2 1) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_2_3 : CutCert G color0 2 3 (cut0 2 3) (side0 2 3) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_2_4 : CutCert G color0 2 4 (cut0 2 4) (side0 2 4) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_2_5 : CutCert G color0 2 5 (cut0 2 5) (side0 2 5) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_2_6 : CutCert G color0 2 6 (cut0 2 6) (side0 2 6) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_2_7 : CutCert G color0 2 7 (cut0 2 7) (side0 2 7) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
end Rainbow
