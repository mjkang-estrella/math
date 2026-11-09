import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert1_3_0 : CutCert Gᶜ color1 3 0 (cut1 3 0) (side1 3 0) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_3_1 : CutCert Gᶜ color1 3 1 (cut1 3 1) (side1 3 1) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_3_2 : CutCert Gᶜ color1 3 2 (cut1 3 2) (side1 3 2) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_3_4 : CutCert Gᶜ color1 3 4 (cut1 3 4) (side1 3 4) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_3_5 : CutCert Gᶜ color1 3 5 (cut1 3 5) (side1 3 5) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_3_6 : CutCert Gᶜ color1 3 6 (cut1 3 6) (side1 3 6) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_3_7 : CutCert Gᶜ color1 3 7 (cut1 3 7) (side1 3 7) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
end Rainbow
