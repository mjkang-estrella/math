import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert1_0_1 : CutCert Gᶜ color1 0 1 (cut1 0 1) (side1 0 1) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_0_2 : CutCert Gᶜ color1 0 2 (cut1 0 2) (side1 0 2) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_0_3 : CutCert Gᶜ color1 0 3 (cut1 0 3) (side1 0 3) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_0_4 : CutCert Gᶜ color1 0 4 (cut1 0 4) (side1 0 4) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_0_5 : CutCert Gᶜ color1 0 5 (cut1 0 5) (side1 0 5) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_0_6 : CutCert Gᶜ color1 0 6 (cut1 0 6) (side1 0 6) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_0_7 : CutCert Gᶜ color1 0 7 (cut1 0 7) (side1 0 7) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
end Rainbow
