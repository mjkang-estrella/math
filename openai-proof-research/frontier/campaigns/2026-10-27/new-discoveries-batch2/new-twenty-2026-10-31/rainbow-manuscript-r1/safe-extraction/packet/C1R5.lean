import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert1_5_0 : CutCert Gᶜ color1 5 0 (cut1 5 0) (side1 5 0) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_5_1 : CutCert Gᶜ color1 5 1 (cut1 5 1) (side1 5 1) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_5_2 : CutCert Gᶜ color1 5 2 (cut1 5 2) (side1 5 2) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_5_3 : CutCert Gᶜ color1 5 3 (cut1 5 3) (side1 5 3) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_5_4 : CutCert Gᶜ color1 5 4 (cut1 5 4) (side1 5 4) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_5_6 : CutCert Gᶜ color1 5 6 (cut1 5 6) (side1 5 6) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_5_7 : CutCert Gᶜ color1 5 7 (cut1 5 7) (side1 5 7) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
end Rainbow
