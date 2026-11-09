import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert0_6_0 : CutCert G color0 6 0 (cut0 6 0) (side0 6 0) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_6_1 : CutCert G color0 6 1 (cut0 6 1) (side0 6 1) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_6_2 : CutCert G color0 6 2 (cut0 6 2) (side0 6 2) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_6_3 : CutCert G color0 6 3 (cut0 6 3) (side0 6 3) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_6_4 : CutCert G color0 6 4 (cut0 6 4) (side0 6 4) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_6_5 : CutCert G color0 6 5 (cut0 6 5) (side0 6 5) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_6_7 : CutCert G color0 6 7 (cut0 6 7) (side0 6 7) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
end Rainbow
