import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert1_2_0 : CutCert Gᶜ color1 2 0 (cut1 2 0) (side1 2 0) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_2_1 : CutCert Gᶜ color1 2 1 (cut1 2 1) (side1 2 1) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_2_3 : CutCert Gᶜ color1 2 3 (cut1 2 3) (side1 2 3) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_2_4 : CutCert Gᶜ color1 2 4 (cut1 2 4) (side1 2 4) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_2_5 : CutCert Gᶜ color1 2 5 (cut1 2 5) (side1 2 5) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_2_6 : CutCert Gᶜ color1 2 6 (cut1 2 6) (side1 2 6) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_2_7 : CutCert Gᶜ color1 2 7 (cut1 2 7) (side1 2 7) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
end Rainbow
