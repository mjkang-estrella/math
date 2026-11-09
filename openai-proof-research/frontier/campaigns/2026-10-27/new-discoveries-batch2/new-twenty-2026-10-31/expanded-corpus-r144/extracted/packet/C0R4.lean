import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert0_4_0 : CutCert G color0 4 0 (cut0 4 0) (side0 4 0) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_4_1 : CutCert G color0 4 1 (cut0 4 1) (side0 4 1) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_4_2 : CutCert G color0 4 2 (cut0 4 2) (side0 4 2) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_4_3 : CutCert G color0 4 3 (cut0 4 3) (side0 4 3) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_4_5 : CutCert G color0 4 5 (cut0 4 5) (side0 4 5) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_4_6 : CutCert G color0 4 6 (cut0 4 6) (side0 4 6) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
theorem cert0_4_7 : CutCert G color0 4 7 (cut0 4 7) (side0 4 7) := by
  dsimp [CutCert, RainbowOn, cut0, side0, color0]
  decide
end Rainbow
