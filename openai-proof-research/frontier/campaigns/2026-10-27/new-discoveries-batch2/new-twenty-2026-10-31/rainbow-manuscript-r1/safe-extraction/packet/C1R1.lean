import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert1_1_0 : CutCert Gᶜ color1 1 0 (cut1 1 0) (side1 1 0) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_1_2 : CutCert Gᶜ color1 1 2 (cut1 1 2) (side1 1 2) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_1_3 : CutCert Gᶜ color1 1 3 (cut1 1 3) (side1 1 3) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_1_4 : CutCert Gᶜ color1 1 4 (cut1 1 4) (side1 1 4) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_1_5 : CutCert Gᶜ color1 1 5 (cut1 1 5) (side1 1 5) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_1_6 : CutCert Gᶜ color1 1 6 (cut1 1 6) (side1 1 6) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_1_7 : CutCert Gᶜ color1 1 7 (cut1 1 7) (side1 1 7) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
end Rainbow
